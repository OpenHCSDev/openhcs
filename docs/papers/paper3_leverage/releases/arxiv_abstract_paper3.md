# arXiv abstract (paper3)

Title: Leverage-Driven Software Architecture: Five Independent Frameworks Select the Same Architectural Ground State

## Abstract (MathJax, arXiv-ready)

```text
We define leverage $L(A) = |\mathrm{Capabilities}(A)| / \mathrm{DOF}(A)$ for software architectures and prove that maximizing leverage, satisfying the Single Source of Truth condition, minimizing structural rank, admitting tractable sufficiency checking, and incurring minimum thermodynamic cost per decision cycle are all equivalent to $\mathrm{DOF}(A) = 1$.

Main Result (Theorem ). For any architecture $A$ with $\mathrm{Cap}(A) > 0$: $$\mathrm{DOF}(A) = 1
\;\iff\; \text{max leverage}
\;\iff\; \text{SSOT}
\;\iff\; \mathrm{srank} = 1
\;\iff\; \text{tractable sufficiency}
\;\iff\; \text{minimum thermodynamic cost}.$$

Engineering corollaries: $\mathrm{DOF} = n$ is isomorphic to a series reliability system with $n$ failure points; expected modification cost is proportional to $\mathrm{DOF}$; minimum edit-energy under Landauer calibration equals $j_{\mathcal{M}} \cdot \mathrm{DOF}(A)$ for explicit $j_{\mathcal{M}} > 0$. These follow from the equivalence and are not independent contributions.

The thermodynamic direction was initially proved conditional on P $\neq$ coNP. `DecisionQuotient` removes this assumption: $E_{\mathrm{decision}} \geq \mathrm{srank} \cdot k_B T \ln 2$ is proved directly from Landauer calibration (BA7), and P $\neq$ NP follows from physical law (LP38: Landauer, finite energy, finite signal speed, nontrivial state space), so the tractability equivalence holds unconditionally under these axioms. The England Replication Inequality is proved (england_replication_inequality): the gap in minimal entropy production between a $k$-copy architecture and a single-source architecture is $\geq k_B \ln k$. No open conjectures remain.

All core theorems are machine-checked in Lean 4 with no `sorry` placeholders, via live imports from `AbstractClassSystem`, `Ssot`, and `DecisionQuotient`. An assumption ledger records all conditional dependencies.

Keywords: software architecture, degrees of freedom, leverage, Single Source of Truth, structural rank, formal verification
```

## Abstract (Unicode, Zenodo-ready)

```text
We define leverage L(A) = |Capabilities(A)|/DOF(A) for software architectures and prove that maximizing leverage, satisfying the Single Source of Truth condition, minimizing structural rank, admitting tractable sufficiency checking, and incurring minimum thermodynamic cost per decision cycle are all equivalent to DOF(A) = 1.

Main Result (Theorem ). For any architecture A with Cap(A) > 0:
DOF(A) = 1 ⇔ max leverage ⇔ SSOT ⇔ srank = 1 ⇔ tractable sufficiency ⇔ minimum thermodynamic cost.

Engineering corollaries: DOF = n is isomorphic to a series reliability system with n failure points; expected modification cost is proportional to DOF; minimum edit-energy under Landauer calibration equals j_(ℳ) ⋅ DOF(A) for explicit j_(ℳ) > 0. These follow from the equivalence and are not independent contributions.

The thermodynamic direction was initially proved conditional on P ≠ coNP. DecisionQuotient removes this assumption: E_(decision) ≥ srank ⋅ k_(B)Tln 2 is proved directly from Landauer calibration (BA7), and P ≠ NP follows from physical law (LP38: Landauer, finite energy, finite signal speed, nontrivial state space), so the tractability equivalence holds unconditionally under these axioms. The England Replication Inequality is proved (england_replication_inequality): the gap in minimal entropy production between a k-copy architecture and a single-source architecture is ≥ k_(B)ln k. No open conjectures remain.

All core theorems are machine-checked in Lean 4 with no sorry placeholders, via live imports from AbstractClassSystem, Ssot, and DecisionQuotient. An assumption ledger records all conditional dependencies.

Keywords: software architecture, degrees of freedom, leverage, Single Source of Truth, structural rank, formal verification
```
