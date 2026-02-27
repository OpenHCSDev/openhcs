import DecisionQuotient.Hardness.CoveringLowerBound

/-!
  Paper 4: Decision-Relevant Uncertainty

  WitnessCheckingDuality.lean

  This module packages the certificate-size lower bound as a
  checking-vs-witnessing duality statement:

  - witness budget `W(n)` = minimum refutation support required for the
    empty-set sufficiency core (`2^(n-1)` from CoveringLowerBound),
  - checking budget `T(n)` = finite pair-family size consumed by a checker.

  Any sound checker must satisfy `T(n) ≥ W(n)`.
-/

namespace DecisionQuotient

/-- Witness budget for the empty-set sufficiency core. -/
def witnessBudgetEmpty (n : ℕ) : ℕ := 2 ^ (n - 1)

/-- Checking budget represented as number of inspected pair witnesses. -/
def checkingBudgetPairs {n : ℕ}
    (P : Finset (BinaryState n × BinaryState n)) : ℕ :=
  P.card

/-- Checking-witnessing duality (budget form):
any sound finite checker for the empty-set core needs at least the witness budget.

This is the direct `T(n) ≥ W(n)` form with
`W(n) = 2^(n-1)` and `T(n) = |P|`. -/
theorem checking_witnessing_duality_budget {n : ℕ}
    (hn : 1 ≤ n)
    (P : Finset (BinaryState n × BinaryState n))
    (hSound :
      ∀ Opt : BinaryState n → Bool,
        (∃ s s', agreeOn s s' (∅ : Finset (Fin n)) ∧ Opt s ≠ Opt s') →
        ∃ p ∈ P, Opt p.1 ≠ Opt p.2) :
    witnessBudgetEmpty n ≤ checkingBudgetPairs P := by
  simpa [witnessBudgetEmpty, checkingBudgetPairs] using
    (checking_witnessing_duality (n := n) hn P hSound)

/-- Contrapositive form:
below the witness budget, no finite checker can be sound on the empty-set core. -/
theorem no_sound_checker_below_witness_budget {n : ℕ}
    (hn : 1 ≤ n)
    (P : Finset (BinaryState n × BinaryState n))
    (hSmall : checkingBudgetPairs P < witnessBudgetEmpty n) :
    ¬ (∀ Opt : BinaryState n → Bool,
        (∃ s s', agreeOn s s' (∅ : Finset (Fin n)) ∧ Opt s ≠ Opt s') →
        ∃ p ∈ P, Opt p.1 ≠ Opt p.2) := by
  intro hSound
  have hNeed : witnessBudgetEmpty n ≤ checkingBudgetPairs P :=
    checking_witnessing_duality_budget (n := n) hn P hSound
  exact (Nat.not_lt_of_ge hNeed) hSmall

/-- Time-form corollary:
if each checked witness contributes to runtime and total runtime is bounded below
by the number of checked pairs, then runtime is lower-bounded by witness budget. -/
theorem checking_time_ge_witness_budget {n : ℕ}
    (hn : 1 ≤ n)
    (P : Finset (BinaryState n × BinaryState n))
    (hSound :
      ∀ Opt : BinaryState n → Bool,
        (∃ s s', agreeOn s s' (∅ : Finset (Fin n)) ∧ Opt s ≠ Opt s') →
        ∃ p ∈ P, Opt p.1 ≠ Opt p.2)
    (T : ℕ)
    (hCheck : checkingBudgetPairs P ≤ T) :
    witnessBudgetEmpty n ≤ T := by
  exact le_trans (checking_witnessing_duality_budget (n := n) hn P hSound) hCheck

end DecisionQuotient
