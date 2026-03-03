# arXiv abstract (paper4)

Title: Verified Polynomial-Time Reductions in Lean 4: Formalizing the Complexity of Decision-Relevant Information

## Abstract (MathJax, arXiv-ready)

```text
We present a Lean 4 formalization of polynomial-time reductions and computational complexity proofs, demonstrated through a comprehensive analysis of decision-relevant information: the problem of identifying which variables matter for optimal decision-making.

Formalization contributions. We develop a reusable framework for expressing Karp reductions, oracle complexity classes, and parameterized hardness in Lean 4. The framework integrates with Mathlib's computability library and provides: (1) bundled reduction types with polynomial-time witnesses; (2) tactics for composing reductions; (3) templates for NP/coNP/\_2\^P membership and hardness proofs.

Verified complexity results. As a case study, we formalize the complexity of the SUFFICIENCY-CHECK problem, determining which coordinates of a decision problem suffice for optimal action. We machine-verify:

- coNP-completeness of sufficiency checking via reduction from TAUTOLOGY [@cook1971complexity]

- Inapproximability within $(1-\varepsilon)\ln n$ via L-reduction from SET-COVER [@feige1998threshold]

- $2^{\Omega(n)}$ lower bounds under ETH via circuit-based arguments [@impagliazzo2001complexity]

- W\[2\]-hardness for the parameterized variant with kernelization lower bounds

- A complexity dichotomy: polynomial time in the explicit-state model for $O(\log |S|)$-size sufficient sets, exponential under ETH in the succinct model for $\Omega(n)$-size

All complexity claims use the input encodings fixed in Section.

The formalization comprises 31898 lines of Lean 4 with 1323 machine-verified theorems/lemmas across 118 files. All reductions include explicit polynomial bounds. We identify proof engineering patterns for complexity theory in dependent type systems and discuss challenges of formalizing computational hardness constructively.

Practical corollaries. The primary contribution is theoretical: a formalized reduction framework and a complete characterization of the core decision-relevant problems in the formal model (coNP/$\Sigma_2^P$ completeness and tractable cases under explicit encoding assumptions). The case study formalizes the principle determining what you need to know is harder than knowing everything. This implies that over-modeling is rational under the model and that "simpler" incomplete tools create more work (the Simplicity Tax Theorem, also machine-verified).

Keywords: Lean 4, formal verification, polynomial-time reductions, coNP-completeness, computational complexity, Mathlib, interactive theorem proving
```

## Abstract (Unicode, Zenodo-ready)

```text
We present a Lean 4 formalization of polynomial-time reductions and computational complexity proofs, demonstrated through a comprehensive analysis of decision-relevant information: the problem of identifying which variables matter for optimal decision-making.

Formalization contributions. We develop a reusable framework for expressing Karp reductions, oracle complexity classes, and parameterized hardness in Lean 4. The framework integrates with Mathlib’s computability library and provides: (1) bundled reduction types with polynomial-time witnesses; (2) tactics for composing reductions; (3) templates for NP/coNP/_2^P membership and hardness proofs.

Verified complexity results. As a case study, we formalize the complexity of the SUFFICIENCY-CHECK problem, determining which coordinates of a decision problem suffice for optimal action. We machine-verify:

• coNP-completeness of sufficiency checking via reduction from TAUTOLOGY

• Inapproximability within (1 − ε)ln n via L-reduction from SET-COVER

• 2^(Ω(n)) lower bounds under ETH via circuit-based arguments

• W[2]-hardness for the parameterized variant with kernelization lower bounds

• A complexity dichotomy: polynomial time in the explicit-state model for O(log |S|)-size sufficient sets, exponential under ETH in the succinct model for Ω(n)-size

All complexity claims use the input encodings fixed in Section.

The formalization comprises 31898 lines of Lean 4 with 1323 machine-verified theorems/lemmas across 118 files. All reductions include explicit polynomial bounds. We identify proof engineering patterns for complexity theory in dependent type systems and discuss challenges of formalizing computational hardness constructively.

Practical corollaries. The primary contribution is theoretical: a formalized reduction framework and a complete characterization of the core decision-relevant problems in the formal model (coNP/Σ₂^(P) completeness and tractable cases under explicit encoding assumptions). The case study formalizes the principle determining what you need to know is harder than knowing everything. This implies that over-modeling is rational under the model and that “simpler” incomplete tools create more work (the Simplicity Tax Theorem, also machine-verified).

Keywords: Lean 4, formal verification, polynomial-time reductions, coNP-completeness, computational complexity, Mathlib, interactive theorem proving
```
