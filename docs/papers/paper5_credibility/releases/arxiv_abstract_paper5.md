# arXiv abstract (paper5)

Title: A Formal Theory of Credibility: Why Assertions of Trustworthiness Decrease Trust

## Abstract (MathJax, arXiv-ready)

```text
Credibility is a physical quantity. This paper grounds signaling theory in the thermodynamics of information processing, deriving computable bounds on rational belief update from Landauer's principle and Paper 4's Counting Gap.

Physical grounding. Signal production cost is measured in joules. By Landauer's principle, each irreversible bit operation costs at minimum $k_B T \ln 2$. A cheap talk signal has cost differential $\Delta = \text{Cost}(s \mid \bot) - \text{Cost}(s \mid \top) = 0$: the energy expenditure to produce the signal is truth-independent. A costly signal has $\Delta > 0$ in joules. Machine-checked proofs achieve $\Delta = \infty$: by Paper 4's Counting Gap ($\varepsilon \cdot N \leq C \Rightarrow N \leq C/\varepsilon$), the false-positive rate $\varepsilon_F \to 0$ of a sound type-checker implies that producing a false compiling proof requires traversing a diverging search space, hence diverging energy.

Theorem (Cheap Talk Bound). For any signal $s$ with $\Delta = 0$, posterior credibility is bounded: $\Pr[C{=}1 \mid s] \leq p/(p + (1-p)q)$, where $p$ is the prior and $q$ is the mimicability of $s$. Text is cheap talk. All meta-assertions about credibility are cheap talk.

Theorem (Emphasis Penalty). Under the signaling equilibrium condition that deceptive agents produce repetitions at least as readily as honest agents, $n$ repeated assertions give $\partial C(c, s_{1..n})/\partial n \leq 0$ for $n > k^$. Additional assertions at $\Delta = 0$ carry no energy cost differential and therefore cannot increase rational credibility past the threshold.

Theorem (Text Credibility Bound). For high-magnitude claims (prior $p < e^{-M^}$), no text string achieves credibility above $\tau < 1$. Rephrasing is energy-neutral; it cannot escape the bound.

Theorem (Costly Signal Escape). As $\Delta \to \infty$, $\Pr[C=1 \mid s] \to 1$. Machine-checked proofs achieve this limit. The cost differential is grounded by the Counting Gap, not assumed.

Corollary (Counting Gap grounds $\Delta_\text{Lean}$). $\Delta_\text{Lean} = \infty$ follows from Paper 4, Theorem 3 (Counting Gap) and Theorem 13 (Energy Lower Bound). The impossibility of compiling a false proof is arithmetic, not a design choice.

Credibility leverage $L_C = \Delta C / \text{Signal Cost}$ is maximized by concentrating energy budget on high-$\Delta$ channels (proofs, demonstrations) and minimizing cheap talk. The theorems are formalized in Lean 4; all Lean proofs compile with 0 sorry.

Keywords: signaling theory, cheap talk, physical information theory, Landauer's principle, Counting Gap, Bayesian epistemology, costly signals, formal verification, Lean 4
```

## Abstract (Unicode, Zenodo-ready)

```text
Credibility is a physical quantity. This paper grounds signaling theory in the thermodynamics of information processing, deriving computable bounds on rational belief update from Landauer’s principle and Paper 4’s Counting Gap.

Physical grounding. Signal production cost is measured in joules. By Landauer’s principle, each irreversible bit operation costs at minimum k_(B)Tln 2. A cheap talk signal has cost differential Δ = Cost(s ∣ ⊥) − Cost(s ∣ ⊤) = 0: the energy expenditure to produce the signal is truth-independent. A costly signal has Δ > 0 in joules. Machine-checked proofs achieve Δ = ∞: by Paper 4’s Counting Gap (ε ⋅ N ≤ C ⇒ N ≤ C/ε), the false-positive rate ε_(F) → 0 of a sound type-checker implies that producing a false compiling proof requires traversing a diverging search space, hence diverging energy.

Theorem (Cheap Talk Bound). For any signal s with Δ = 0, posterior credibility is bounded: Pr [C = 1 ∣ s] ≤ p/(p + (1 − p)q), where p is the prior and q is the mimicability of s. Text is cheap talk. All meta-assertions about credibility are cheap talk.

Theorem (Emphasis Penalty). Under the signaling equilibrium condition that deceptive agents produce repetitions at least as readily as honest agents, n repeated assertions give ∂C(c, s_(1..n))/∂n ≤ 0 for n > k^(*). Additional assertions at Δ = 0 carry no energy cost differential and therefore cannot increase rational credibility past the threshold.

Theorem (Text Credibility Bound). For high-magnitude claims (prior p < e^(−M^(*))), no text string achieves credibility above τ < 1. Rephrasing is energy-neutral; it cannot escape the bound.

Theorem (Costly Signal Escape). As Δ → ∞, Pr [C = 1 ∣ s] → 1. Machine-checked proofs achieve this limit. The cost differential is grounded by the Counting Gap, not assumed.

Corollary (Counting Gap grounds Δ_(Lean)). Δ_(Lean) = ∞ follows from Paper 4, Theorem 3 (Counting Gap) and Theorem 13 (Energy Lower Bound). The impossibility of compiling a false proof is arithmetic, not a design choice.

Credibility leverage L_(C) = ΔC/Signal Cost is maximized by concentrating energy budget on high-Δ channels (proofs, demonstrations) and minimizing cheap talk. The theorems are formalized in Lean 4; all Lean proofs compile with 0 sorry.

Keywords: signaling theory, cheap talk, physical information theory, Landauer’s principle, Counting Gap, Bayesian epistemology, costly signals, formal verification, Lean 4
```
