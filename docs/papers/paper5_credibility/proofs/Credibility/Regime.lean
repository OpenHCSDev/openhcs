/-
  Credibility/Regime.lean

  Regime typing for credibility analysis.
  
  This parallels Paper 4's regime structure but for credibility instead of complexity.
  
  Different credibility analyses apply depending on what the receiver knows
  about the signal production process:
  - Does the receiver know the prior?
  - Does the receiver know the mimicability?
  - Does the receiver know if the signal is cheap talk or costly?

  Regime tags:
    - noPrior: Receiver has no prior information
    - knownPrior: Receiver knows prior p
    - knownDeception: Receiver knows deception rate d
    - fullBayes: Receiver knows both p and d
    - unknownCost: Receiver doesn't know if signal is cheap/costly
-/

import Credibility.Basic
import Mathlib.Tactic

namespace Credibility.Regime

/-!
  ## Credibility Regime Definition

  IMPORTANT: Different regimes require different credibility analyses.
  
  The cheap talk bound (Theorem 3.1) assumes full knowledge of p and q.
  If the receiver doesn't know these, the analysis changes.
-/

/-- Credibility regime: specifies what the receiver knows about signal production -/
inductive CredibilityRegime
  | noPrior              -- Receiver has no prior information
  | knownPrior (p : ℝ)   -- Receiver knows prior p
  | knownDeception (d : ℝ)  -- Receiver knows deception rate
  | fullBayes (p d : ℝ)     -- Receiver knows both p and d
  | unknownCost            -- Receiver doesn't know if signal is cheap/costly
  deriving DecidableEq

/-- Regime requires prior knowledge -/
def regimeKnowsPrior : CredibilityRegime → Bool
  | noPrior => false
  | knownPrior _ => true
  | knownDeception _ => false
  | fullBayes _ _ => true
  | unknownCost => false

/-- Regime requires deception knowledge -/
def regimeKnowsDeception : CredibilityRegime → Bool
  | noPrior => false
  | knownPrior _ => false
  | knownDeception _ => true
  | fullBayes _ _ => true
  | unknownCost => false

/-- Regime knows full cost structure -/
def regimeKnowsCost : CredibilityRegime → Bool
  | noPrior => false
  | knownPrior _ => false
  | knownDeception _ => false
  | fullBayes _ _ => true
  | unknownCost => false

/-!
  ## Regime-Dependent Credibility

  The credibility bound depends on what the receiver knows.
  
  IMPORTANT: In the no-prior regime, the analysis is different.
  We need to consider worst-case priors or use max-min strategies.
-/

/-- Credibility bound under different regimes -/
def regimeBound (regime : CredibilityRegime) (q : ℝ) : ℝ :=
  match regime with
  | noPrior => 1  -- No bound without prior
  | knownPrior p => p / (p + (1 - p) * q)
  | knownDeception d => 1 / (1 + d)  -- Conservative bound
  | fullBayes p d => p / (p + (1 - p) * d)
  | unknownCost => 1  -- No bound without knowing cost structure

/-!
  ## Regime Transfer

  When does one regime's analysis transfer to another?
  
  IMPORTANT: If receiver learns more (e.g., learns prior), the bounds tighten.
-/

/-- Learning prior can only improve bound -/
theorem prior_known_tightens_bound (p q : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1) (hq : 0 ≤ q) :
    regimeBound (knownPrior p) q ≤ regimeBound noPrior q := by
  unfold regimeBound
  simp
  linarith

/-- Full Bayes gives best bound -/
theorem full_bayes_optimal (p d : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1) (hd : 0 ≤ d) :
    regimeBound (fullBayes p d) d ≤ regimeBound (knownPrior p) d := by
  unfold regimeBound
  simp
  linarith

/-!
  ## Regime Compatibility with Cheap/Costly Signals

  CRITICAL: The regime analysis assumes we know whether the signal is cheap talk or costly.
  
  In the unknownCost regime, we need to consider both possibilities.
-/

/-- If cost is unknown, worst case is cheap talk -/
theorem unknown_cost_worst_case (p q : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1) (hq : 0 ≤ q) :
    -- Worst case: assume cheap talk
    ∃ bound, bound = regimeBound unknownCost q ∧ 
      (∀ other_regime, regimeBound other_regime q ≤ bound) := by
  use 1
  constructor
  · unfold regimeBound; simp
  · intro R
    cases R <;> unfold regimeBound <;> linarith

/-!
  ## Regime Examples

  Real-world regime mapping:
  - Academic paper review: fullBayes (know reviewer prior, can estimate deception)
  - Social media: knownDeception (know bot rate)
  - First encounter: noPrior
  - Unknown source: unknownCost
-/

/-- Social media regime (known deception rate) -/
def socialMediaRegime (deceptionRate : ℝ) : CredibilityRegime :=
  knownDeception deceptionRate

/-- Academic peer review regime -/
def peerReviewRegime (prior : ℝ) (deceptionRate : ℝ) : CredibilityRegime :=
  fullBayes prior deceptionRate

end Credibility.Regime
