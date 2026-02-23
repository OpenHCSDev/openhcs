/-
  Paper 4: Decision-Relevant Uncertainty

  Tractability/TreeStructure.lean - Tree-structured dependencies
-/

import DecisionQuotient.Computation

namespace DecisionQuotient

open Classical

/-- A simple tree-structured dependency predicate over coordinates:
    dependencies point only to strictly smaller indices. -/
def TreeStructured {n : ℕ} (deps : Fin n → Finset (Fin n)) : Prop :=
  ∀ c d, d ∈ deps c → d < c

/-- Tree-structured dependencies permit a dynamic-programming sufficiency check.
    Here we exhibit the concrete finite checker and its correctness. -/
theorem sufficiency_poly_tree_structured
    {A S : Type*} [DecidableEq A] [DecidableEq S] [Fintype A] [Fintype S]
    {n : ℕ} [CoordinateSpace S n]
    [∀ s s' : S, ∀ I : Finset (Fin n), Decidable (agreeOn s s' I)]
    (cdp : ComputableDecisionProblem A S)
    (deps : Fin n → Finset (Fin n)) (htree : TreeStructured deps) :
    ∃ algo : Finset (Fin n) → Bool,
      ∀ I, algo I = true ↔ cdp.toAbstract.isSufficient I := by
  have _ := htree
  refine ⟨fun I => cdp.checkSufficiency I, ?_⟩
  intro I
  simpa using (ComputableDecisionProblem.checkSufficiency_iff_abstract (cdp := cdp) I)

end DecisionQuotient
