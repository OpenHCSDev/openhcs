# arXiv abstract (paper4b)

Title: Stochastic and Sequential Regimes: Extending the Decision Quotient to Dynamic Information Sufficiency

## Abstract (MathJax, arXiv-ready)

```text
We extend the static decision quotient framework of Paper 4 to stochastic and sequential regimes. Given a decision problem with actions $A$, factored state space $S = X_1 \times \cdots \times X_n$, and utility $U$, we ask: what complexity is required to identify sufficient coordinate sets when (a) the state is drawn from a distribution $P$, or (b) decisions unfold over time with transitions and observations?

Results:

- Stochastic regime: STOCHASTIC-SUFFICIENCY-CHECK is PP-complete via MAJSAT reduction. Tractable under product distributions, bounded support, log-concave.

- Sequential regime: SEQUENTIAL-SUFFICIENCY-CHECK is PSPACE-complete via TQBF reduction. Tractable under full observability, bounded horizon, tree structure.

- Regime hierarchy: Static $\subset$ Stochastic $\subset$ Sequential; coNP $\subset$ PP $\subset$ PSPACE.

- Substrate cost: The integrity-competence verdict is substrate-independent; trajectories diverge based on substrate cost $\kappa$.

- Temporal learning: Bayesian structure detection reduces abstention over time.

- Temporal integrity: Evidence-monotone retractions preserve integrity across sequences.

The reduction constructions are machine-checked in Lean 4 (3552 lines, 124 theorems).

Keywords: computational complexity, decision theory, stochastic decision problems, POMDPs, polynomial hierarchy, PSPACE
```

## Abstract (Unicode, Zenodo-ready)

```text
We extend the static decision quotient framework of Paper 4 to stochastic and sequential regimes. Given a decision problem with actions A, factored state space S = X₁ × ⋯ × X_(n), and utility U, we ask: what complexity is required to identify sufficient coordinate sets when (a) the state is drawn from a distribution P, or (b) decisions unfold over time with transitions and observations?

Results:

• Stochastic regime: STOCHASTIC-SUFFICIENCY-CHECK is PP-complete via MAJSAT reduction. Tractable under product distributions, bounded support, log-concave.

• Sequential regime: SEQUENTIAL-SUFFICIENCY-CHECK is PSPACE-complete via TQBF reduction. Tractable under full observability, bounded horizon, tree structure.

• Regime hierarchy: Static ⊂ Stochastic ⊂ Sequential; coNP ⊂ PP ⊂ PSPACE.

• Substrate cost: The integrity-competence verdict is substrate-independent; trajectories diverge based on substrate cost κ.

• Temporal learning: Bayesian structure detection reduces abstention over time.

• Temporal integrity: Evidence-monotone retractions preserve integrity across sequences.

The reduction constructions are machine-checked in Lean 4 (3552 lines, 124 theorems).

Keywords: computational complexity, decision theory, stochastic decision problems, POMDPs, polynomial hierarchy, PSPACE
```
