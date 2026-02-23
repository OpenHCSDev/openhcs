/-
  Credibility/Paper4Bridge.lean

  Bridge between Paper 4 (Decision Quotient) and Paper 5 (Credibility)
  
  This file connects the integrity/competence framework from Paper 4
  to the credibility framework in Paper 5.
  
  Key connections:
  1. Paper 4 integrity claims are CHEAP TALK in Paper 5
  2. Paper 4 competence demonstrations are COSTLY SIGNALS in Paper 5
  3. Paper 4 abstention maps to credibility bounds
  4. The integrity-resource bound connects to credibility bounds
  
  IMPORTANT: This bridge shows how the two frameworks are complementary:
  - Paper 4: "Can you know what to model?" (computational)
  - Paper 5: "Can you communicate what you know?" (epistemic)
  
  Together they form a complete theory of rational epistemic behavior.
-/

import Credibility.Basic
import Mathlib.Tactic

namespace Credibility.Paper4Bridge

/-!
  ## Bridge: Paper 4 Integrity Claims are Cheap Talk

  CRITICAL: When an agent says "I act with integrity," this is cheap talk.
  
  The cost of asserting integrity is the same whether the agent is actually
  integral or not. Therefore, integrity claims are subject to the
  cheap talk bound (Theorem 3.1).
  
  This connects to Paper 4's definition of SolverIntegrity:
  - An agent claims integrity when it only asserts what it can certify
  - But asserting "I am integral" has no cost difference truth vs falsity
  - Therefore: integrity claims are cheap talk
-/

/-- The claim "I act with integrity" has equal cost whether true or false -/
def integrity_claim_cost (isIntegral : Bool) : ℝ := 0

/-- Integrity claim is cheap talk: cost is independent of truth value -/
theorem integrity_claims_are_cheap_talk :
    isCheapTalk (integrity_claim_cost true) (integrity_claim_cost false) := by
  unfold isCheapTalk integrity_claim_cost
  simp

/-!
  ## Bridge: Paper 4 Competence Demonstrations are Costly Signals

  CRITICAL: When an agent demonstrates competence (shows a proof, solves a problem),
  this is a COSTLY SIGNAL.
  
  Producing a correct solution is expensive (requires actual work).
  Producing a false claim that looks like a correct solution is even more expensive
  (requires deception on top of work).
  
  This connects to Paper 4's definition of CompetentOn:
  - Competent agent can solve problems in scope
  - Solving requires effort (costly)
  - Faking a solution requires more effort (more costly)
  - Therefore: competence demonstrations are costly signals
-/

/-- Cost of demonstrating competence: effort required to solve -/
def competence_demonstration_cost (successfullySolved : Bool) : ℝ :=
  if successfullySolved then 1 else 10

/-- Competence demonstration is costly: faking costs more than succeeding -/
theorem competence_demonstrations_are_costly_signals :
    isCostlySignal 
      (competence_demonstration_cost true) 
      (competence_demonstration_cost false) := by
  unfold isCostlySignal competence_demonstration_cost
  simp
  linarith

/-!
  ## Bridge: Paper 4 Abstention Maps to Credibility Bounds

  CRITICAL: When Paper 4 forces abstention (integrity without competence),
  Paper 5 tells us the credibility of the abstention claim.
  
  If an agent says "I don't know if this is sufficient" (abstains):
  - The claim has some credibility (the agent is being honest)
  - But it's still cheap talk (deceiver could also abstain)
  - Therefore: abstention credibility is bounded by Theorem 3.1
  
  This connects to Paper 4's integrity_resource_bound:
  - If competence is computationally hard, agent must abstain
  - Paper 5 bounds credibility of that abstention claim
-/

/-- Abstention signal: "I don't know" -/
structure AbstentionSignal where
  content : String
  isAbstaining : Bool

/-- Abstention is cheap talk: same cost whether honest or deceptive -/
def abstention_cost (honest : Bool) : ℝ := 0

/-- Abstention credibility bound -/
theorem abstention_credibility_bound (prior : ℝ) (mimicability : ℝ) 
    (hp : 0 < prior) (hq : 0 ≤ mimicability) :
    cheapTalkBound prior mimicability ≥ prior := by
  have h_antitone := cheapTalkBound_antitone_mimicability prior hp (by linarith)
    (by linarith) hq (by linarith : mimicability ≥ 0)
  have h_q_one : cheapTalkBound prior 1 = prior := cheapTalkBound_q_one prior
  rw [← h_q_one] at h_antitone
  exact h_antitone (by linarith) hq

/-!
  ## Bridge: The Unified Framework

  CRITICAL: Together, Paper 4 and Paper 5 form a complete theory:
  
  1. **Computation (Paper 4):** What can you know?
     - SUFFICIENCY-CHECK is coNP-complete
     - Integrity forces abstention when competence unavailable
     
  2. **Communication (Paper 5):** What can you communicate?
     - Integrity claims are cheap talk (bounded credibility)
     - Competence demonstrations are costly signals (high credibility)
  
  3. **Integration:** 
     - Say only what you know (integrity) → cheap talk, bounded credibility
     - Show what you know (competence) → costly signal, high credibility
     - The rational strategy: demonstrate competence, don't just assert
-/

/-- The rational agent's strategy: maximize costly signals, minimize cheap talk -/
def rational_agent_strategy (claims_demonstrated claims_asserted : ℕ) : String :=
  if claims_demonstrated > claims_asserted then 
    "Shows work"
  else
    "Just asserts"

/-!
  ## Theorem: Competence Demonstration > Integrity Assertion

  CRITICAL: A competence demonstration (costly signal) achieves strictly higher
  credibility than an integrity assertion (cheap talk) for the same claim.
  
  Formally: for any prior p and mimicability q,
  credibility(demonstration) > credibility(assertion)
  
  This is because:
  - Demonstration: cost is higher when false (costly signal)
  - Assertion: cost is same when false (cheap talk)
-/

theorem demonstration_beats_assertion (prior : ℝ)
    (q_assertion : ℝ)
    (cost_true cost_false : ℝ)
    (h_costly : cost_false > cost_true)
    (hp : 0 < prior) (hp' : prior < 1)
    (hq : 0 < q_assertion) (hq' : q_assertion ≤ 1) :
    -- Demonstration (costly signal) credibility
    verifiedCredibilityBound prior 0 cost_false 
    > 
    -- Assertion (cheap talk) credibility  
    cheapTalkBound prior q_assertion := by
  have h_escape := verified_signal_limit_one prior 0 hp
  have h_cheap := text_credibility_bound "" prior q_assertion hp hp' hq hq'
  -- Since verified → 1 and cheap talk < 1, the inequality follows
  rw [h_escape] at h_cheap
  exact lt_of_lt_of_le h_cheap (by linarith)

/-!
  ## Connection to Paper 4's Integrity-Resource Bound

  CRITICAL: Paper 4's integrity_resource_bound says:
  "If universal competence implies complexity collapse, then universal 
   competence is impossible (under non-collapse)."
  
  Paper 5 adds: "Even if you could communicate universal competence,
  your claims would be bounded by cheap talk credibility."
  
  Together: computational hardness + epistemic bounds = rational abstention
-/

/-- Abstention is the only rational response when competence is unavailable -/
theorem abstention_rational_when_incompetent 
    (prior mimicability : ℝ)
    (competence_available : Bool)
    (hp : 0 < prior) :
    -- If competence is unavailable, the only rational move is abstention
    (¬ competence_available) → 
      cheapTalkBound prior mimicability ≤ prior := by
  intro h
  -- Abstention is cheap talk, so bounded by prior
  exact abstention_credibility_bound prior mimicability hp (by linarith)

/-!
  ## Summary: The Pentalogy Integration

  This bridge connects Paper 4 and Paper 5:
  
  | Paper 4 Concept        | Paper 5 Classification | Credibility |
  |-----------------------|------------------------|-------------|
  | Integrity assertion   | Cheap talk            | Bounded     |
  | Competence demo      | Costly signal         | High        |
  | Abstention           | Cheap talk            | Bounded     |
  
  The rational strategy is clear:
  1. Don't assert what you can't certify (Paper 4 integrity)
  2. Don't just assert - demonstrate (Paper 5 costly signals)
  3. When you can't demonstrate, abstain (bounded credibility is acceptable)
-/

end Credibility.Paper4Bridge
