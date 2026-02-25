# arXiv abstract (paper4_toc)

Title: Computational Complexity of Physical Information Sufficiency

## Abstract (MathJax, arXiv-ready)

```text
We study physical information sufficiency as a decision-theoretic meta-problem. For $\mathcal{D}=(A,S,U)$ with factored state space $S=X_1\times\cdots\times X_n$, a coordinate set $I$ is sufficient when $$s_I=s'_I \implies \operatorname{Opt}(s)=\operatorname{Opt}(s').$$ This asks whether projected information preserves the full optimal-action correspondence.

Complexity landscape.

- SUFFICIENCY-CHECK is coNP-complete; MINIMUM-SUFFICIENT-SET is coNP-complete; ANCHOR-SUFFICIENCY is $\Sigma_{2}^{P}$-complete. Informally, this gap separates verification (checking whether a given coordinate set suffices) from discovery (finding a grounding under which the optimal action is determined), and suggests the latter is structurally harder unless the polynomial hierarchy collapses.

- Under explicit-state encoding, polynomial-time algorithms hold for bounded actions, separable utility, and tree-structured utility.

- Under succinct encoding, hardness is regime-dependent: with ETH, there are worst-case families with $k^*=n$ requiring $2^{\Omega(n)}$ time.

- Under query access, the finite-state core has worst-case Opt-oracle complexity $\Omega(|S|)$, with Boolean value-entry and state-batch refinements preserving the obstruction.

Physical grounding. The paper formalizes a physical-to-core encoding $E:\mathcal{P}\to\mathcal{D}$ and a transport rule: declared physical assumptions transfer to core assumptions, and core claims lift back to encoded physical instances. Encoded physical counterexamples induce core failures on the encoded slice. Discrete-time interface semantics (decision event = one tick) and budgeted thermodynamic lifts (bit lower bounds to energy/carbon lower bounds under declared constants) are formalized in the same assumption-typed framework.
All theorem-level claims are machine-checked in Lean 4 (19529 lines, 847 theorem/lemma statements). Complexity-class completeness follows by composition with standard complexity results; regime-dependent and physical-transport consequences are proved as assumption-explicit closures.

Keywords: computational complexity, physical information, decision theory, polynomial hierarchy, formal verification
```

## Abstract (Unicode, Zenodo-ready)

```text
We study physical information sufficiency as a decision-theoretic meta-problem. For 𝒟 = (A, S, U) with factored state space S = X₁ × ⋯ × X_(n), a coordinate set I is sufficient when
s_(I) = s′_(I) ⟹ Opt (s) = Opt (s′).
This asks whether projected information preserves the full optimal-action correspondence.

Complexity landscape.

• SUFFICIENCY-CHECK is coNP-complete; MINIMUM-SUFFICIENT-SET is coNP-complete; ANCHOR-SUFFICIENCY is Σ₂^(P)-complete. Informally, this gap separates verification (checking whether a given coordinate set suffices) from discovery (finding a grounding under which the optimal action is determined), and suggests the latter is structurally harder unless the polynomial hierarchy collapses.

• Under explicit-state encoding, polynomial-time algorithms hold for bounded actions, separable utility, and tree-structured utility.

• Under succinct encoding, hardness is regime-dependent: with ETH, there are worst-case families with k^(*) = n requiring 2^(Ω(n)) time.

• Under query access, the finite-state core has worst-case Opt-oracle complexity Ω(|S|), with Boolean value-entry and state-batch refinements preserving the obstruction.

Physical grounding. The paper formalizes a physical-to-core encoding E: 𝒫 → 𝒟 and a transport rule: declared physical assumptions transfer to core assumptions, and core claims lift back to encoded physical instances. Encoded physical counterexamples induce core failures on the encoded slice. Discrete-time interface semantics (decision event = one tick) and budgeted thermodynamic lifts (bit lower bounds to energy/carbon lower bounds under declared constants) are formalized in the same assumption-typed framework.

All theorem-level claims are machine-checked in Lean 4 (19529 lines, 847 theorem/lemma statements). Complexity-class completeness follows by composition with standard complexity results; regime-dependent and physical-transport consequences are proved as assumption-explicit closures.

Keywords: computational complexity, physical information, decision theory, polynomial hierarchy, formal verification
```
