# arXiv abstract (paper1_jsait)

Title: Identification Capacity and Rate-Query Tradeoffs in Classification Systems

## Abstract (MathJax, arXiv-ready)

```text
We study zero-error class identification under constrained observations with three resources: tag rate $L$ (bits per entity), identification cost $W$ (attribute queries), and distortion $D$ (misidentification probability). We prove an information barrier: if the attribute-profile map $\pi$ is not injective on classes, then attribute-only observation cannot identify class identity with zero error. Let $A_\pi:= \max_u |\{c: \pi(c)=u\}|$ be collision multiplicity. Any $D=0$ scheme must satisfy $L \ge \log_2 A_\pi$, and this bound is tight. In maximal-barrier domains ($A_\pi=k$), the nominal point $(L,W,D)=(\lceil\log_2 k\rceil,O(1),0)$ is the unique Pareto-optimal zero-error point. Without tags ($L=0$), zero-error identification requires $W=\Omega(d)$ queries, where $d$ is the distinguishing dimension (worst case $d=n$, so $W=\Omega(n)$). Minimal sufficient query sets form the bases of a matroid, making $d$ well-defined and linking the model to zero-error source coding via graph entropy. We also state fixed-axis incompleteness: a fixed observation axis is complete only for axis-measurable properties. Results instantiate to databases, biology, typed software systems, and model registries, and are machine-checked in Lean 4 (6707 lines, 296 theorem/lemma statements, 0 `sorry`).

**Keywords:** rate-distortion theory, identification capacity, zero-error source coding, query complexity, matroid structure, classification systems
```

## Abstract (Unicode, Zenodo-ready)

```text
We study zero-error class identification under constrained observations with three resources: tag rate L (bits per entity), identification cost W (attribute queries), and distortion D (misidentification probability). We prove an information barrier: if the attribute-profile map π is not injective on classes, then attribute-only observation cannot identify class identity with zero error. Let A_(π):= max_(u)|{c: π(c) = u}| be collision multiplicity. Any D = 0 scheme must satisfy L ≥ log₂A_(π), and this bound is tight. In maximal-barrier domains (A_(π) = k), the nominal point (L, W, D) = (⌈log₂k⌉, O(1), 0) is the unique Pareto-optimal zero-error point. Without tags (L = 0), zero-error identification requires W = Ω(d) queries, where d is the distinguishing dimension (worst case d = n, so W = Ω(n)). Minimal sufficient query sets form the bases of a matroid, making d well-defined and linking the model to zero-error source coding via graph entropy. We also state fixed-axis incompleteness: a fixed observation axis is complete only for axis-measurable properties. Results instantiate to databases, biology, typed software systems, and model registries, and are machine-checked in Lean 4 (6707 lines, 296 theorem/lemma statements, 0 sorry).

Keywords: rate-distortion theory, identification capacity, zero-error source coding, query complexity, matroid structure, classification systems
```
