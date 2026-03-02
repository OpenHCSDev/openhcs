# arXiv abstract (paper2_it)

Title: Zero-Incoherence Capacity of Interactive Encoding Systems: Achievability, Converse, and Side Information Bounds

## Abstract (MathJax, arXiv-ready)

```text
Single-Source Coherence Theorem. We prove that among all possible degrees of freedom (DOF = number of independent encoding locations), exactly one value (DOF = 1) guarantees coherence. DOF = 0 fails (no fact encoded). DOF $\geq$ 2 fails (permits explicit construction of inconsistency). Only DOF = 1 satisfies both requirements.

Proof Sketch. Case analysis on $\mathbb{N}$: For DOF = 1, any two queries return the single location's value; transitivity of equality forces agreement. For DOF $\geq$ 2, construct two locations with values $v$ and $v' \neq v$; queries return different answers. This witness construction works uniformly for all DOF $\geq$ 2. By trichotomy of naturals, DOF = 1 is the unique solution.

We introduce the zero-incoherence capacity: the maximum rate guaranteeing zero disagreement among replicated encodings. Main results: exact capacity ($C_0=1$), tight side-information bound ($\geq\log_2 k$ bits for $k$-way incoherence), and rate-complexity separation ($O(1)$ at capacity vs $\Omega(n)$ above).

Encoding locations are terminals in multi-terminal source coding. Derivation is perfect correlation reducing effective rate; only complete derivation achieves zero incoherence. We give achievability and converse proofs, formalize confusability/incoherence graphs, and present the mutual-information side-information bound.

Constructive instantiations (programming patterns, software case study) supplement theory. Extended evaluation, code, and Lean proofs (6300+ lines, 0 `sorry`) are in supplementary material.

Index Terms: zero-error capacity, multi-terminal source coding, side information, confusability graph, impossibility theorems
```

## Abstract (Unicode, Zenodo-ready)

```text
Single-Source Coherence Theorem. We prove that among all possible degrees of freedom (DOF = number of independent encoding locations), exactly one value (DOF = 1) guarantees coherence. DOF = 0 fails (no fact encoded). DOF ≥ 2 fails (permits explicit construction of inconsistency). Only DOF = 1 satisfies both requirements.

Proof Sketch. Case analysis on ℕ: For DOF = 1, any two queries return the single location’s value; transitivity of equality forces agreement. For DOF ≥ 2, construct two locations with values v and v′ ≠ v; queries return different answers. This witness construction works uniformly for all DOF ≥ 2. By trichotomy of naturals, DOF = 1 is the unique solution.

We introduce the zero-incoherence capacity: the maximum rate guaranteeing zero disagreement among replicated encodings. Main results: exact capacity (C₀ = 1), tight side-information bound ( ≥ log₂k bits for k-way incoherence), and rate-complexity separation (O(1) at capacity vs Ω(n) above).

Encoding locations are terminals in multi-terminal source coding. Derivation is perfect correlation reducing effective rate; only complete derivation achieves zero incoherence. We give achievability and converse proofs, formalize confusability/incoherence graphs, and present the mutual-information side-information bound.

Constructive instantiations (programming patterns, software case study) supplement theory. Extended evaluation, code, and Lean proofs (6300+ lines, 0 sorry) are in supplementary material.

Index Terms: zero-error capacity, multi-terminal source coding, side information, confusability graph, impossibility theorems
```
