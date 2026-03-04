# arXiv abstract (paper4)

Title: Decision Quotient: Foundations and Complexity of Decision-Relevant Information

## Abstract (MathJax, arXiv-ready)

```text
We study decision-relevant information: which coordinates of a state space suffice to determine the optimal action. For a decision problem $\mathcal{D}=(A,S,U)$ with $S=X_1 \times \cdots \times X_n$, a coordinate set $I$ is sufficient if $s_I=s'_I$ implies $\operatorname{Opt}(s)=\operatorname{Opt}(s')$. The associated optimizer quotient records the coarsest abstraction that preserves optimal-action distinctions.

Under the encoding model fixed in Section, we prove that [Sufficiency-Check]{.smallcaps} is coNP-complete, [Minimum-Sufficient-Set]{.smallcaps} is coNP-complete, and [Anchor-Sufficiency]{.smallcaps} is $\Sigma_{2}^{P}$-complete. We also prove an encoding-sensitive dichotomy: explicit-state instances with logarithmic-size sufficient sets admit polynomial-time algorithms, while succinctly encoded instances with linear-size sufficient sets inherit ETH-conditioned exponential lower bounds. In addition, we isolate tractable subcases for bounded actions, separable utility, low tensor rank, tree structure, bounded treewidth, and coordinate symmetry.

These results also yield direct corollaries for exact simplification tasks: in the general succinct regime, exact behavior-preserving minimization has no polynomial-time worst-case solution unless $P=coNP$, while conservative over-specification can be a rational response when exact pruning carries exponential cost.

The Lean 4 development mechanizes the core reductions and theorem statements, with 44497 lines, 1872 theorems/lemmas, and 179 proof files.
```

## Abstract (Unicode, Zenodo-ready)

```text
We study decision-relevant information: which coordinates of a state space suffice to determine the optimal action. For a decision problem 𝒟 = (A, S, U) with S = X₁ × ⋯ × Xₙ, a coordinate set I is sufficient if s_I = s′_(I) implies Opt (s) = Opt (s′). The associated optimizer quotient records the coarsest abstraction that preserves optimal-action distinctions.

Under the encoding model fixed in Section, we prove that SUFFICIENCY-CHECK is coNP-complete, MINIMUM-SUFFICIENT-SET is coNP-complete, and ANCHOR-SUFFICIENCY is Σ₂ᴾ-complete. We also prove an encoding-sensitive dichotomy: explicit-state instances with logarithmic-size sufficient sets admit polynomial-time algorithms, while succinctly encoded instances with linear-size sufficient sets inherit ETH-conditioned exponential lower bounds. In addition, we isolate tractable subcases for bounded actions, separable utility, low tensor rank, tree structure, bounded treewidth, and coordinate symmetry.

These results also yield direct corollaries for exact simplification tasks: in the general succinct regime, exact behavior-preserving minimization has no polynomial-time worst-case solution unless P = coNP, while conservative over-specification can be a rational response when exact pruning carries exponential cost.

The Lean 4 development mechanizes the core reductions and theorem statements, with 44497 lines, 1872 theorems/lemmas, and 179 proof files.
```
