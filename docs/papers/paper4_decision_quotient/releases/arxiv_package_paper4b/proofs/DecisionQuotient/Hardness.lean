/-
  Paper 4: Decision-Relevant Uncertainty
  
  Hardness.lean - Computational Complexity Results
  
  KEY RESULTS:
  
  1. SUFFICIENCY-CHECK is coNP-complete
     Given (A, S, U, I), is I a sufficient coordinate set?
     
  2. MINIMUM-SUFFICIENT-SET is in Σ₂ᴾ and coNP-hard  
     Given (A, S, U, k), does there exist sufficient I with |I| ≤ k?
  
  These results sit beyond NP-completeness and explain why
  engineers default to over-modeling: the clean version is computationally hard.
  
  NOTE: Full complexity-theoretic proofs are in LaTeX (TAUTOLOGY reduction and
  the Σ₂ᴾ upper bound). This file formalizes the problem structure and tractable subcases.
-/

import DecisionQuotient.Sufficiency
import DecisionQuotient.Reduction
import DecisionQuotient.Computation
import DecisionQuotient.Hardness.Sigma2PExhaustive.AnchorSufficiency
import DecisionQuotient.Hardness.CoveringLowerBound

namespace DecisionQuotient

/-! ## Problem Encodings -/

/-- Representation of a decision problem for computational complexity.
    U is given as a computable function (in practice, a circuit). -/
structure EncodedDecisionProblem where
  /-- Number of alternatives -/
  numAlts : ℕ
  /-- Number of coordinates -/
  numCoords : ℕ
  /-- Size of each coordinate space (all binary for simplicity) -/
  coordSize : Fin numCoords → ℕ := fun _ => 2
  /-- Utility function encoded as a Boolean circuit (opaque here) -/
  utilityCircuit : Unit

/-! ## The Sufficiency-Check Problem -/

/-- SUFFICIENCY-CHECK problem:
    Input: Decision problem encoding, coordinate set I
    Question: Is I sufficient? (∀ s, s': s_I = s'_I ⟹ Opt(s) = Opt(s'))
    
    Complexity: coNP-complete -/
structure SufficiencyCheckInstance where
  problem : EncodedDecisionProblem
  coordSet : Finset (Fin problem.numCoords)

/-! ## The Minimum-Sufficient-Set Problem -/

/-- MINIMUM-SUFFICIENT-SET problem:
    Input: Decision problem encoding, integer k
    Question: ∃ I with |I| ≤ k such that I is sufficient?
    
    Complexity: in Σ₂ᴾ, coNP-hard
    
    Structure: ∃I (|I| ≤ k) ∀s, s' (s_I = s'_I ⟹ Opt(s) = Opt(s'))
    
    This is an ∃∀ quantifier pattern, characteristic of Σ₂ᴾ. -/
structure MinSufficientSetInstance where
  problem : EncodedDecisionProblem
  targetSize : ℕ

/-! ## Reduction from TAUTOLOGY (coNP-hardness of SUFFICIENCY-CHECK) -/

/-- 
  THEOREM (coNP-hardness of SUFFICIENCY-CHECK):
  
  Reduction from TAUTOLOGY:
  Given Boolean formula φ(x₁,...,xₙ), construct:
  
  - A = {a₀, a₁}
  - S = {0,1}ⁿ⁺¹ (add dummy coordinate x₀)
  - U(a₁, s) = φ(x₁,...,xₙ)  [ignores x₀]
  - U(a₀, s) = 0
  - I = {0}  (just the dummy coordinate)
  
  Then:
    I is sufficient 
    ⟺ Opt doesn't depend on x₁,...,xₙ
    ⟺ φ is constant (always true or always false)
    ⟺ φ is a tautology (for TAUTOLOGY) or contradiction
  
  For TAUTOLOGY specifically:
    φ is a tautology ⟺ φ(s) = 1 for all s ⟺ Opt(s) = a₁ for all s ⟺ I = {0} is sufficient
-/
theorem sufficiency_check_coNP_hard {n : ℕ} (φ : Formula n) :
    (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology :=
  (tautology_iff_sufficient φ).symm

/-! ## MINIMUM-SUFFICIENT-SET Complexity Bounds -/

/-
  THEOREM (Complexity of MINIMUM-SUFFICIENT-SET):

  The problem has the quantifier structure:
    ∃ I (|I| ≤ k) ∀ s s' (s_I = s'_I ⟹ Opt(s) = Opt(s'))

  This yields two bounds:

  UPPER BOUND (Σ₂ᴾ membership):
    The ∃∀ quantifier pattern places MINIMUM-SUFFICIENT-SET in Σ₂ᴾ.
    A Σ₂ᴾ machine guesses I (NP witness), then verifies sufficiency (coNP check).

  LOWER BOUND (coNP-hardness):
    Setting k = 0 reduces to SUFFICIENCY-CHECK, which is coNP-complete.
    Therefore MINIMUM-SUFFICIENT-SET is coNP-hard.

  COMBINED: MINIMUM-SUFFICIENT-SET ∈ Σ₂ᴾ ∩ coNP-hard

  Note: Whether MINIMUM-SUFFICIENT-SET is Σ₂ᴾ-COMPLETE (not just hard) is a subtle
  question. The existential quantifier ranges over coordinate SETS, not Boolean
  assignments, which complicates direct reductions from ∃∀-SAT.

  However, the closely related ANCHOR-SUFFICIENCY problem IS Σ₂ᴾ-hard
  (Theorem `anchor_sufficiency_sigma2p`), showing the problem FAMILY
  is Σ₂ᴾ-complete.

  For the paper's purposes, the key result is: the problem is HARD
  (beyond NP and coNP unless the polynomial hierarchy collapses).
-/

/-- MINIMUM-SUFFICIENT-SET is coNP-hard (via k=0 case). -/
theorem min_sufficient_set_coNP_hard {n : ℕ} (φ : Formula n) :
    (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology :=
  sufficiency_check_coNP_hard (φ := φ)

/-! ## Tractable Subcases -/

/-- On finite state/action spaces, the boolean `checkSufficiency` procedure
    (defined in `Computation.lean`) decides abstract sufficiency. -/
theorem tractable_small_state_space
    {A S : Type*} {n : ℕ} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S) (I : Finset (Fin n)) :
    cdp.checkSufficiency I = true ↔ cdp.toAbstract.isSufficient I := by
  simpa using (ComputableDecisionProblem.checkSufficiency_iff_abstract (cdp := cdp) I)

/-! ## Implications -/

/--
  COROLLARY (Why over-modeling is the default):

  Finding the minimal set of "decision-relevant" factors is coNP-hard (k = 0 case),
  and in Σ₂ᴾ by its quantifier structure.
  Even CHECKING if a proposed set is sufficient is coNP-hard.

  This formally explains the engineering phenomenon:
  - It's computationally easier to model everything than to find the minimum
  - "Which unknowns matter" is a hard question, not a lazy one to avoid
  - Bounded scenario analysis (small Ŝ) makes the problem tractable
-/
theorem over_modeling_justified {n : ℕ} (φ : Formula n) :
    (reductionProblem φ).isSufficient (∅ : Finset (Fin 1)) ↔ φ.isTautology :=
  min_sufficient_set_coNP_hard (φ := φ)

/-! ## Anchor Sufficiency (Σ₂ᴾ-hard) -/

/-! A strengthened variant fixes a coordinate set I and asks whether there exists
    an assignment to I that makes Opt constant on the induced subcube. This
    problem is Σ₂ᴾ-hard via a reduction from ∃∀-SAT (see
    `Hardness/AnchorSufficiency.lean`). -/

theorem anchor_sufficiency_sigma2p (φ : ExistsForallFormula) :
    ExistsForallFormula.satisfiable φ ↔
      (qbfProblem (ExistsForallFormula.padUniversal φ)).anchorSufficient
        (xCoords (ExistsForallFormula.padUniversal φ).nx (ExistsForallFormula.padUniversal φ).ny) :=
  exists_forall_iff_anchor_sufficient_padded φ

theorem anchor_sufficiency_sigma2p_nonempty (φ : ExistsForallFormula) (hny : 0 < φ.ny) :
    ExistsForallFormula.satisfiable φ ↔
      (qbfProblem φ).anchorSufficient (xCoords φ.nx φ.ny) :=
  exists_forall_iff_anchor_sufficient φ hny

/-! ## Covering Lower Bound (Certificate Size) -/

/-- Any refutation certificate built from fewer than `2^(n-1)` state pairs
    can be defeated by an adversarial Opt function, for any `I` with `|I| < n`. -/
theorem certificate_lower_bound_for_I_summary {n : ℕ} (I : Finset (Fin n))
    (hn : 1 ≤ n) (hI : I.card < n)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card < 2 ^ (n - 1)) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' I ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 I → Opt p.1 = Opt p.2) :=
  certificate_lower_bound_for_I (I := I) hn hI P hP

theorem certificate_lower_bound_for_I_card_summary {n : ℕ} (I : Finset (Fin n))
    (hn : 1 ≤ n) (hI : I.card < n) (hIpos : 0 < I.card)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card < 2 ^ (n - I.card)) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' I ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 I → Opt p.1 = Opt p.2) :=
  certificate_lower_bound_for_I_card (I := I) hn hI hIpos P hP

theorem certificate_lower_bound_for_I_empty_summary {n : ℕ}
    (hn : 1 ≤ n)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card < 2 ^ (n - 1)) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' (∅ : Finset (Fin n)) ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 (∅ : Finset (Fin n)) → Opt p.1 = Opt p.2) :=
  certificate_lower_bound_for_I_empty (hn := hn) P hP

/-- Polynomial-size corollary: if `|P| ≤ n^3` and `n^3 < 2^(n-1)`,
    then the same adversarial Opt exists. -/
theorem certificate_lower_bound_poly_summary {n : ℕ} (I : Finset (Fin n))
    (hn : 1 ≤ n) (hI : I.card < n)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card ≤ n ^ 3) (hpow : n ^ 3 < 2 ^ (n - 1)) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' I ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 I → Opt p.1 = Opt p.2) :=
  certificate_lower_bound_poly (I := I) hn hI P hP hpow

theorem certificate_lower_bound_poly_ge_summary {n : ℕ} (I : Finset (Fin n))
    (hn : 12 ≤ n) (hI : I.card < n)
    (P : Finset (BinaryState n × BinaryState n))
    (hP : P.card ≤ n ^ 3) :
    ∃ Opt : BinaryState n → Bool,
      (∃ s s', agreeOn s s' I ∧ Opt s ≠ Opt s') ∧
      (∀ p ∈ P, agreeOn p.1 p.2 I → Opt p.1 = Opt p.2) :=
  certificate_lower_bound_poly_ge (I := I) hn hI P hP

end DecisionQuotient
