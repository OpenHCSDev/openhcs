# arXiv abstract (paper4_toc)

Title: Computational Complexity of Physical Counting

## Abstract (MathJax, arXiv-ready)

```text
Abstract

We characterize which coordinates of a factored state space determine optimal actions. For decision problem $\mathcal{D}=(A,S,U)$ with $S=X_1\times\cdots\times X_n$, coordinate set $I$ is sufficient if $s_I=s'_I\Rightarrow\operatorname{Opt}(s)=\operatorname{Opt}(s')$.

We prove fourteen first-principles theorems: thirteen from pure mathematics and logic, one from empirical assumption (temperature). The decision quotient $Q=S/{\sim}$ (where $s\sim s'\Leftrightarrow\operatorname{Opt}(s)=\operatorname{Opt}(s')$) is the minimal abstraction: any other abstraction preserving optimal actions factors uniquely through $Q$. Verification has a lower bound: any sound checker for the empty-set sufficiency core requires $\geq 2^{n-1}$ witness pairs. The foundational chain from counting measure to probability to Bayes' theorem to the Decision Quotient follows from finite set cardinality. Fisher information, entropy bounds, optimal transport, rate-distortion, and thermodynamics each independently recover $\mathrm{srank}$ as the fundamental decision complexity measure.

Complexity classifications: SUFFICIENCY-CHECK and MINIMUM-SUFFICIENT-SET are coNP-complete; ANCHOR-SUFFICIENCY is $\Sigma_2^P$-complete; stochastic and sequential variants are PP- and PSPACE-complete respectively, with strict static $\subset$ stochastic $\subset$ sequential separation. Six structural subcases admit polynomial algorithms. Under ETH, succinct encodings carry $2^{\Omega(n)}$ lower bounds.

Bayesian updating is optimal: from $\log x\leq x-1$ alone we prove it uniquely minimizes expected log loss.

Two results carry empirical conditions. Conditional on Landauer's principle ($k_BT\ln 2$ per irreversible bit erasure, experimentally supported since 1961), composed with the bit-operation lower bounds above, the inequality $dU\geq\lambda\,dC$ follows by multiplication; rejecting it requires rejecting Landauer. Conditional on stochastic thermodynamics (Barato--Seifert 2015), the thermodynamic uncertainty relation $\mathrm{Var}(J)/\langle J\rangle^2\geq 2/\sigma$ bounds decision precision by entropy production, with minimal $\sigma$ scaling with $\mathrm{srank}$.

All results are machine-checked in Lean 4 with no `sorry` placeholders. Complexity results carry their hypotheses as explicit Lean theorem parameters. A machine-generated assumption ledger records all conditional dependencies. There are no hidden axioms.
```

## Abstract (Unicode, Zenodo-ready)

```text
Abstract

We characterize which coordinates of a factored state space determine optimal actions. For decision problem 𝒟 = (A, S, U) with S = X₁ × ⋯ × X_(n), coordinate set I is sufficient if s_(I) = s′_(I) ⇒ Opt (s) = Opt (s′).

We prove fourteen first-principles theorems: thirteen from pure mathematics and logic, one from empirical assumption (temperature). The decision quotient Q = S/∼ (where s ∼ s′ ⇔ Opt (s) = Opt (s′)) is the minimal abstraction: any other abstraction preserving optimal actions factors uniquely through Q. Verification has a lower bound: any sound checker for the empty-set sufficiency core requires ≥ 2^(n − 1) witness pairs. The foundational chain from counting measure to probability to Bayes’ theorem to the Decision Quotient follows from finite set cardinality. Fisher information, entropy bounds, optimal transport, rate-distortion, and thermodynamics each independently recover srank as the fundamental decision complexity measure.

Complexity classifications: SUFFICIENCY-CHECK and MINIMUM-SUFFICIENT-SET are coNP-complete; ANCHOR-SUFFICIENCY is Σ₂^(P)-complete; stochastic and sequential variants are PP- and PSPACE-complete respectively, with strict static ⊂ stochastic ⊂ sequential separation. Six structural subcases admit polynomial algorithms. Under ETH, succinct encodings carry 2^(Ω(n)) lower bounds.

Bayesian updating is optimal: from log x ≤ x − 1 alone we prove it uniquely minimizes expected log loss.

Two results carry empirical conditions. Conditional on Landauer’s principle (k_(B)Tln 2 per irreversible bit erasure, experimentally supported since 1961), composed with the bit-operation lower bounds above, the inequality dU ≥ λ dC follows by multiplication; rejecting it requires rejecting Landauer. Conditional on stochastic thermodynamics (Barato–Seifert 2015), the thermodynamic uncertainty relation Var(J)/⟨J⟩² ≥ 2/σ bounds decision precision by entropy production, with minimal σ scaling with srank.

All results are machine-checked in Lean 4 with no sorry placeholders. Complexity results carry their hypotheses as explicit Lean theorem parameters. A machine-generated assumption ledger records all conditional dependencies. There are no hidden axioms.
```
