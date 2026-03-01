# Paper: Leverage-Driven Software Architecture: Five Independent Frameworks Select the Same Architectural Ground State

**Status**: Draft-ready | **Lean**: 3691 lines, 201 theorems

---

## Abstract

Five independent scientific frameworks---engineering optimization, epistemic coherence, information geometry, computational complexity, and statistical physics---each characterize the same architectural property: having exactly one degree of freedom.

**Central Result (Five-Way Equivalence, Theorem [\[thm:five-way\]](#thm:five-way){reference-type="ref" reference="thm:five-way"}).** For any architecture $A$ with $\mathrm{Cap}(A) > 0$: $$\mathrm{DOF}(A) = 1
\;\iff\; \text{max leverage}
\;\iff\; \text{SSOT}
\;\iff\; \mathrm{srank} = 1
\;\iff\; \text{tractable sufficiency}
\;\iff\; \text{zero thermodynamic cost}.$$ This convergence is not a coincidence. The five frameworks are logically independent---each was developed for a distinct purpose---yet all select the single-source condition as their ground state. All equivalences are machine-checked in Lean 4 via live cross-paper imports (Paper 3 $\to$ Paper 4 $\to$ Mathlib).

Building on axis orthogonality (Paper 1) and Single Source of Truth (Paper 2), the engineering consequences follow: define leverage $$L(A) = \frac{|\mathrm{Capabilities}(A)|}{\mathrm{DOF}(A)}.$$ Maximizing $L$ subject to feasibility minimizes expected error probability (DOF--Reliability Isomorphism), minimizes modification cost (Leverage Gap), and minimizes physical edit-energy under Landauer calibration with explicit per-edit constant $j_{\mathcal{M}} > 0$. These are *corollaries* of the convergence theorem, not independent contributions.

**Open Conjectures.** The thermodynamic selection theorem currently assumes P $\neq$ coNP. We conjecture that thermodynamic cost scales directly with structural rank *unconditionally*---removing the complexity-theoretic hypothesis would reduce the five-way equivalence to a purely physical statement. A second open problem connects DOF $=1$ architectures to England's replication inequality: single-source architectures that generate derived instances may satisfy a formal entropy-production bound that multi-DOF architectures cannot match.

All core theorems are machine-checked in Lean 4. An assumption ledger and proof listing accompany the paper.

Keywords: software architecture, degrees of freedom, five-way equivalence, Landauer principle, structural rank, formal methods


_Failed to convert lean_stats.tex_

# Introduction

## The Central Discovery

Five independent scientific frameworks each characterize the same architectural property.

::: theorem
[]{#thm:five-way label="thm:five-way"} For any architecture $A$ with $\mathrm{Cap}(A) > 0$, the following are equivalent: $$\underbrace{\mathrm{DOF}(A) = 1}_{\text{single source}}
\;\iff\;
\underbrace{L(A) \text{ is maximal}}_{\text{engineering}}
\;\iff\;
\underbrace{\mathrm{SSOT}(A)}_{\text{epistemics}}
\;\iff\;
\underbrace{\mathrm{srank}(A) = 1}_{\text{information}}
\;\iff\;
\underbrace{\text{tractable sufficiency}}_{\text{complexity}}
\;\iff\;
\underbrace{\text{zero thermodynamic cost}}_{\text{physics}}$$
:::

This is proved in Section [\[five-way-equivalence\]](#five-way-equivalence){reference-type="ref" reference="five-way-equivalence"} and machine-checked in Lean 4 via live cross-paper imports (Paper 3 $\to$ Paper 4 $\to$ Mathlib).

**Why this is surprising.** Each framework was developed independently for a different purpose: leverage for architectural optimization, SSOT for epistemic coherence, structural rank for decision theory, tractability for computational complexity, thermodynamic cost for statistical physics. They are logically independent---knowing one gives no *a priori* reason to expect the others. Their convergence on a single condition is the central result of the paper.

## Engineering Consequences

The following results are corollaries of the five-way equivalence, not independent contributions.

**Definition (Leverage):** $L(A) = |\mathrm{Capabilities}(A)| / \mathrm{DOF}(A)$.

1.  **DOF--Reliability Isomorphism (Theorem [\[thm:dof-reliability\]](#thm:dof-reliability){reference-type="ref" reference="thm:dof-reliability"}):** Architecture with $n$ DOF is isomorphic to series system with $n$ components. Each DOF is a failure point.

2.  **Leverage--Error Tradeoff (Theorem [\[thm:leverage-error\]](#thm:leverage-error){reference-type="ref" reference="thm:leverage-error"}):** Among architectures with equal capabilities, $L(A_1) > L(A_2) \implies P_{\mathrm{error}}(A_1) < P_{\mathrm{error}}(A_2)$.

3.  **Modification Complexity Gap (Theorem [\[thm:leverage-gap\]](#thm:leverage-gap){reference-type="ref" reference="thm:leverage-gap"}):** At fixed capabilities, expected modification cost is proportional to DOF.

4.  **Physical Edit-Energy Floor (Theorem [\[thm:physical-energy-floor\]](#thm:physical-energy-floor){reference-type="ref" reference="thm:physical-energy-floor"}):** Under Landauer calibration with explicit constant $j_\mathcal{M} > 0$, minimum edit-energy equals $j_\mathcal{M} \cdot \mathrm{DOF}(A)$.

5.  **Optimal Architecture (Theorem [\[thm:optimal\]](#thm:optimal){reference-type="ref" reference="thm:optimal"}):** $f(R) = \arg\max_{A:\,\mathrm{Cap}(A) \supseteq R} L(A)$ minimizes expected error and is computable.

These constitute a formal proof that architectural optimization is decidable, with a provably optimal selection procedure. But their deeper content is that they all reduce to the DOF count---which the five-way equivalence explains from five independent first principles.

## Open Conjectures

Two open problems remain within reach of the existing formalization machinery.

**Conjecture 1 (Unconditional Thermodynamic Selection).** Theorem [\[thm:thermodynamic-selection\]](#thm:thermodynamic-selection){reference-type="ref" reference="thm:thermodynamic-selection"} assumes P $\neq$ coNP to derive mandatory energy cost for DOF $>1$ architectures. We conjecture the result holds unconditionally: thermodynamic cost scales directly with $\mathrm{srank}$, bypassing complexity theory. This would reduce the five-way equivalence to a chain of physical necessities with no complexity-theoretic hypothesis.

**Conjecture 2 (England Replication Bound).** Single-source architectures (DOF $=1$) that generate derived instances are analogous to self-replicating systems in non-equilibrium thermodynamics. England's inequality [@england2013statistical] bounds entropy production of such systems. We conjecture a formal analog: the entropy cost of maintaining consistency across $n$ replicated DOF strictly exceeds the entropy cost of a single DOF by a factor of at least $n$, with the bound tight at DOF $=1$.

**Conjecture 3 (Wolpert Bound).** Wolpert and Kolchinsky's general thermodynamic bounds [@wolpert2019stochastic] suggest cost scales with the number of relevant decision coordinates---i.e., with $\mathrm{srank}$---with an explicit constant derivable from Landauer calibration. We conjecture this gives a quantitative thermodynamic cost formula $\Omega(\mathrm{srank} \cdot k_B T \ln 2)$ per decision cycle, removing the existential witness and giving a closed-form bound.

## Dependency Chain

This paper does not subsume Papers 1 and 2---it builds on them.

1.  **Paper 1** proves axis orthogonality $\to$ enables error independence (Theorem [\[thm:error-independence\]](#thm:error-independence){reference-type="ref" reference="thm:error-independence"})

2.  **Paper 2** proves DOF $= 1$ guarantees SSOT coherence $\to$ establishes the second equivalence

3.  **Paper 4** proves tractability boundary and thermodynamic lift $\to$ establishes the fourth and fifth equivalences

4.  **This paper** closes the chain: leverage maximization (Framework 1) is equivalent to all of the above

Paper 2 supplies the coherence constraint (DOF $= 1$ per structural fact); this paper supplies the optimization rule inside the feasible set (maximize leverage) and proves that rule is selected by four additional independent frameworks.

## Organization

Section [\[foundations\]](#foundations){reference-type="ref" reference="foundations"} defines Architecture, DOF, Capabilities, and Leverage. Section [\[probability-model\]](#probability-model){reference-type="ref" reference="probability-model"} derives the error model. Section [\[main-theorems\]](#main-theorems){reference-type="ref" reference="main-theorems"} proves decidability and optimality. Section [\[instances\]](#instances){reference-type="ref" reference="instances"} demonstrates SSOT, nominal typing, microservices, APIs, and databases as leverage instances. Section [\[five-way-equivalence\]](#five-way-equivalence){reference-type="ref" reference="five-way-equivalence"} proves the central five-way equivalence and states the open conjectures. Section [\[appendix-lean\]](#appendix-lean){reference-type="ref" reference="appendix-lean"} describes the Lean mechanization.

## Scope

Leverage characterizes the capability-to-DOF ratio. Performance, security, and other dimensions remain orthogonal concerns. Error independence is *derived* from Paper 1's axis orthogonality theorem, not assumed. Physical edit-energy claims use a single explicit calibration constant ($j_\mathcal{M} > 0$) and no additional architectural axioms beyond the DOF--Reliability Isomorphism.


# Foundations

We formalize the core concepts: architecture state spaces, degrees of freedom, capabilities, and leverage.

## Architecture State Space

::: definition
[]{#def:architecture label="def:architecture"} An *architecture* is a tuple $A = (C, S, T, R)$ where:

-   $C$ is a finite set of *components* (modules, services, endpoints, etc.)

-   $S = \prod_{c \in C} S_c$ is the *state space* (product of component state spaces)

-   $T : S \to \mathcal{P}(S)$ defines valid *transitions* (state changes)

-   $R$ is a set of *requirements* the architecture must satisfy
:::

**Intuition:** An architecture consists of components, each with a state space. The total state space is the product of component spaces. Transitions define how the system can evolve.

::: example
-   $C = \{U, O, P\}$ where $U=\text{UserService}$, $O=\text{OrderService}$, $P=\text{PaymentService}$

-   $S_{\text{UserService}} = \text{UserDB} \times \text{Endpoints} \times \text{Config}$

-   Similar for other services

-   $S = S_{\text{UserService}} \times S_{\text{OrderService}} \times S_{\text{PaymentService}}$
:::

## Degrees of Freedom

::: definition
[]{#def:dof label="def:dof"} The *degrees of freedom* of architecture $A = (C, S, T, R)$ is: $$\text{DOF}(A) = \dim(S)$$ the dimension of the state space.
:::

**Operational meaning:** DOF counts independent modification points. If $\text{DOF}(A) = n$, then $n$ independent changes can be made to the architecture.

::: proposition
[]{#prop:dof-additive label="prop:dof-additive"} For disjoint architectures $A_1 = (C_1, S_1, T_1, R_1)$ and $A_2 = (C_2, S_2, T_2, R_2)$ with $C_1 \cap C_2 = \emptyset$: $$\text{DOF}(A_1 \oplus A_2) = \text{DOF}(A_1) + \text{DOF}(A_2)$$ where $A_1 \oplus A_2 = (C_1 \cup C_2, S_1 \times S_2, T_1 \times T_2, R_1 \cup R_2)$.
:::

::: proof
*Proof.* $\dim(S_1 \times S_2) = \dim(S_1) + \dim(S_2)$ by standard linear algebra. ◻
:::

::: example
1.  **Monolith:** Single deployment unit $\to$ DOF $= 1$

2.  **$n$ Microservices:** $n$ independent services $\to$ DOF $= n$

3.  **Copied Code:** Code duplicated to $n$ locations $\to$ DOF $= n$ (each copy independent)

4.  **SSOT:** Single source, $n$ derived uses $\to$ DOF $= 1$ (only source is independent)

5.  **$k$ API Endpoints:** $k$ independent definitions $\to$ DOF $= k$

6.  **$m$ Config Parameters:** $m$ independent settings $\to$ DOF $= m$
:::

## Capabilities

::: definition
[]{#def:capabilities label="def:capabilities"} The *capability set* of architecture $A$ is: $$\text{Cap}(A) = \{r \in R \mid A \text{ satisfies } r\}$$
:::

**Examples of capabilities:**

-   "Support horizontal scaling"

-   "Provide type provenance"

-   "Enable independent deployment"

-   "Satisfy single source of truth for class definitions"

-   "Allow polyglot persistence"

::: definition
[]{#def:satisfies label="def:satisfies"} Architecture $A$ *satisfies* requirement $r$ (written $A \vDash r$) if there exists an execution trace in $(S, T)$ that meets $r$'s specification.
:::

## Leverage

::: definition
[]{#def:leverage label="def:leverage"} The *leverage* of architecture $A$ is: $$L(A) = \frac{|\text{Cap}(A)|}{\text{DOF}(A)}$$
:::

**Special cases:**

1.  **Infinite Leverage ($L = \infty$):** Unlimited capabilities from single source (metaprogramming)

2.  **Unit Leverage ($L = 1$):** Linear relationship (n capabilities from n DOF)

3.  **Sublinear Leverage ($L < 1$):** Antipattern (more DOF than capabilities)

::: example
-   **SSOT:** DOF $= 1$, Cap $= \{F, \text{uses of } F\}$ where $|$uses$| \to \infty$\
    $\Rightarrow L = \infty$

-   **Scattered Code (n copies):** DOF $= n$, Cap $= \{F\}$\
    $\Rightarrow L = 1/n$ (antipattern!)

-   **Generic REST Endpoint:** DOF $= 1$, Cap $= \{\text{serve } n \text{ use cases}\}$\
    $\Rightarrow L = n$

-   **Specific Endpoints:** DOF $= n$, Cap $= \{\text{serve } n \text{ use cases}\}$\
    $\Rightarrow L = 1$
:::

::: definition
[]{#def:dominance label="def:dominance"} Architecture $A_1$ *dominates* $A_2$ (written $A_1 \succeq A_2$) if:

1.  $\text{Cap}(A_1) \supseteq \text{Cap}(A_2)$ (at least same capabilities)

2.  $L(A_1) \geq L(A_2)$ (at least same leverage)

$A_1$ *strictly dominates* $A_2$ (written $A_1 \succ A_2$) if $A_1 \succeq A_2$ with at least one inequality strict.
:::

## Modification Complexity

::: definition
[]{#def:mod-complexity label="def:mod-complexity"} For requirement change $\delta R$, the *modification complexity* is: $$M(A, \delta R) = \text{expected number of independent changes to implement } \delta R$$
:::

::: theorem
[]{#thm:mod-bound label="thm:mod-bound"} For all architectures $A$ and requirement changes $\delta R$: $$M(A, \delta R) \leq \text{DOF}(A)$$ with equality when $\delta R$ affects all components.
:::

::: proof
*Proof.* Each change modifies at most one DOF. Since there are $\text{DOF}(A)$ independent modification points, the maximum number of changes is $\text{DOF}(A)$. ◻
:::

::: example
Consider changing a structural fact $F$ with $n$ use sites:

-   **SSOT:** $M = 1$ (change at source, derivations update automatically)

-   **Scattered:** $M = n$ (must change each copy independently)
:::

## Formalization in Lean

All definitions in this section are formalized in `Leverage/Foundations.lean`:

-   `Architecture`: Structure with components, state, transitions, requirements

-   `Architecture.leverage`: Leverage metric

-   `Architecture.dominates`: Dominance relation

-   `compose_dof`: Proposition [\[prop:dof-additive\]](#prop:dof-additive){reference-type="ref" reference="prop:dof-additive"}

-   `modification_eq_dof`: Theorem [\[thm:mod-bound\]](#thm:mod-bound){reference-type="ref" reference="thm:mod-bound"}


# Probability Model

We derive the relationship between DOF and error probability from Paper 1's axis independence theorem.

## Error Independence from Axis Orthogonality

The independence of errors is not an axiom---it is a consequence of axis orthogonality proven in Paper 1 [@paper1_typing_discipline].

::: theorem
[]{#thm:error-independence label="thm:error-independence"} If axes $\{A_1, \ldots, A_n\}$ are orthogonal (Paper 1, Theorem `minimal_complete_unique_orthogonal`), then errors along each axis are statistically independent.
:::

::: proof
*Proof.* By Paper 1's orthogonality theorem, orthogonal axes satisfy: $$\forall i \neq j: A_i \perp A_j \quad (\text{no axis constrains another})$$

An *error along axis $A_i$* is a deviation from specification in the dimension $A_i$ controls. By orthogonality:

-   Deviation along $A_i$ does not affect the value along $A_j$

-   The probability of error in $A_i$ is independent of the state of $A_j$

Therefore: $$P(\text{error in } A_i \land \text{error in } A_j) = P(\text{error in } A_i) \cdot P(\text{error in } A_j)$$

This is the definition of statistical independence. ◻
:::

::: corollary
[]{#cor:dof-errors label="cor:dof-errors"} DOF$(A) = n$ implies $n$ independent sources of error, each with probability $p$.
:::

::: proof
*Proof.* DOF counts independent axes (Paper 2, Definition [\[def:dof\]](#def:dof){reference-type="ref" reference="def:dof"}). By Theorem [\[thm:error-independence\]](#thm:error-independence){reference-type="ref" reference="thm:error-independence"}, independent axes have independent errors. ◻
:::

::: theorem
[]{#thm:error-compound label="thm:error-compound"} For a system to be correct, all $n$ independent axes must be error-free. Errors compound multiplicatively.
:::

::: proof
*Proof.* By Paper 2's coherence theorem (`oracle_arbitrary`), incoherence in any axis violates system correctness. An error in axis $A_i$ introduces incoherence along $A_i$. Therefore, correctness requires $\bigwedge_{i=1}^{n} \neg\text{error}(A_i)$. By Theorem [\[thm:error-independence\]](#thm:error-independence){reference-type="ref" reference="thm:error-independence"}, this probability is $(1-p)^n$. ◻
:::

## Error Probability Formula

::: theorem
[]{#thm:error-prob label="thm:error-prob"} For architecture with $n$ DOF and per-component error rate $p$: $$P_{\text{error}}(n) = 1 - (1-p)^n$$
:::

::: proof
*Proof.* By Theorem [\[thm:error-independence\]](#thm:error-independence){reference-type="ref" reference="thm:error-independence"} (derived from Paper 1's orthogonality), each DOF has independent error probability $p$, so each is correct with probability $(1-p)$. By Theorem [\[thm:error-compound\]](#thm:error-compound){reference-type="ref" reference="thm:error-compound"}, all $n$ DOF must be correct: $$P_{\text{correct}}(n) = (1-p)^n$$ Therefore: $$P_{\text{error}}(n) = 1 - P_{\text{correct}}(n) = 1 - (1-p)^n$$ ◻
:::

::: corollary
[]{#cor:linear-approx label="cor:linear-approx"} For fixed $p>0$, the linear expected-error model and the exact series model induce the same ordering on architectures by DOF.
:::

::: proof
*Proof.* By Theorem [\[thm:approx-bound\]](#thm:approx-bound){reference-type="ref" reference="thm:approx-bound"}, ordering equivalence is exact under the discrete model used in the mechanization. ◻
:::

::: corollary
[]{#cor:dof-monotone label="cor:dof-monotone"} For architectures $A_1, A_2$: $$\text{DOF}(A_1) < \text{DOF}(A_2) \implies P_{\text{error}}(A_1) < P_{\text{error}}(A_2)$$
:::

::: proof
*Proof.* $P_{\text{error}}(n) = 1 - (1-p)^n$ is strictly increasing in $n$ for $p \in (0,1)$. ◻
:::

## Expected Errors

::: theorem
[]{#thm:expected-errors label="thm:expected-errors"} Expected number of errors in architecture $A$: $$\mathbb{E}[\text{\# errors}] = p \cdot \text{DOF}(A)$$
:::

::: proof
*Proof.* By linearity of expectation: $$\mathbb{E}[\text{\# errors}] = \sum_{i=1}^{\text{DOF}(A)} P(\text{error in DOF}_i) = \sum_{i=1}^{\text{DOF}(A)} p = p \cdot \text{DOF}(A)$$ ◻
:::

::: example
Assume $p = 0.01$ (1% per-component error rate):

-   DOF $= 1$: $P_{\text{error}} = 1 - 0.99 = 0.01$ (1%)

-   DOF $= 10$: $P_{\text{error}} = 1 - 0.99^{10} \approx 0.096$ (9.6%)

-   DOF $= 100$: $P_{\text{error}} = 1 - 0.99^{100} \approx 0.634$ (63.4%)
:::

## Connection to Reliability Theory

The error model has a direct interpretation in classical reliability theory [@patterson2013computer], connecting software architecture to a mature mathematical framework with 60+ years of theoretical development.

::: theorem
[]{#thm:dof-reliability label="thm:dof-reliability"} An architecture with DOF $= n$ is *isomorphic* to a series reliability system with $n$ components. The isomorphism:

1.  **Preserves ordering:** If $\text{DOF}(A_1) < \text{DOF}(A_2)$, then $P_{\text{error}}(A_1) < P_{\text{error}}(A_2)$

2.  **Is invertible:** Round-trip mapping preserves DOF exactly

3.  **Connects domains:** $P_{\text{error}}(n) = 1 - R_{\text{series}}(n)$ where $R_{\text{series}}(n) = (1-p)^n$
:::

**Interpretation:** Each DOF is a "component" that must work correctly. This is the reliability analog of Theorem [\[thm:error-independence\]](#thm:error-independence){reference-type="ref" reference="thm:error-independence"}, which derives error independence from axis orthogonality.

::: theorem
[]{#thm:approx-bound label="thm:approx-bound"} For architectures $A_1,A_2$ with equal capabilities and error rate $p>0$, the linear model and the exact series model induce the same DOF ordering: $$\text{DOF}(A_1)\le \text{DOF}(A_2)
\iff
(\mathbb{E}[\text{errors}(A_1)]\cdot d)\le(\mathbb{E}[\text{errors}(A_2)]\cdot d),$$ where $d$ is the denominator of the discrete error-rate representation.
:::

::: proof
*Proof.* This is theorem `ordering_equivalence_exact` in `Leverage/Probability.lean`. ◻
:::

**Linear Approximation Justification:** For small $p$ (the software engineering regime where $p \approx 0.01$), the linear model $P_{\text{error}} \approx n \cdot p$ is:

1.  Order-equivalent to the exact series model in the mechanized discrete representation

2.  Monotone in DOF for fixed positive error rate

3.  Cleanly formalized in natural-number arithmetic

## Epistemic Grounding

The probability model is not axiomatic---it is derived from the epistemic foundations established in Papers 1 and 2:

1.  **Paper 1** proves axis orthogonality (`minimal_complete_unique_orthogonal`)

2.  **Theorem [\[thm:error-independence\]](#thm:error-independence){reference-type="ref" reference="thm:error-independence"}** derives error independence from orthogonality

3.  **Paper 2** establishes that DOF = 1 guarantees coherence (Theorem `oracle_arbitrary`)

4.  **Theorem [\[thm:error-compound\]](#thm:error-compound){reference-type="ref" reference="thm:error-compound"}** connects errors to incoherence

This derivation chain ensures the probability model rests on proven foundations, not assumed axioms.

## Leverage Gap: Quantitative Predictions

The leverage framework provides *quantitative*, empirically testable predictions about modification costs.

::: theorem
[]{#thm:leverage-gap label="thm:leverage-gap"} For architectures with equal capabilities, the modification cost ratio equals the inverse leverage ratio: $$\frac{\text{ModCost}(A_2)}{\text{ModCost}(A_1)} = \frac{\text{DOF}(A_2)}{\text{DOF}(A_1)} = \frac{L(A_1)}{L(A_2)}$$
:::

::: theorem
[]{#thm:testable-prediction label="thm:testable-prediction"} If architecture $A_1$ has $n\times$ lower DOF than $A_2$ (for equal capabilities), then $A_1$ requires $n\times$ fewer expected modifications. This is empirically testable against PR/commit data.
:::

::: corollary
[]{#cor:dof-ratio label="cor:dof-ratio"} The ratio of expected errors between two architectures equals the ratio of their DOF: $$\frac{\mathbb{E}[\text{errors}(A_2)]}{\mathbb{E}[\text{errors}(A_1)]} = \frac{\text{DOF}(A_2)}{\text{DOF}(A_1)}$$
:::

These theorems transform architectural intuitions into testable hypotheses. A claim that "Pattern X is 3× better than Pattern Y" can be verified by comparing DOF and measuring modification frequency in real codebases.

## Formalization

Formalized in `Leverage/Probability.lean`:

-   `dof_reliability_isomorphism`: Theorem [\[thm:dof-reliability\]](#thm:dof-reliability){reference-type="ref" reference="thm:dof-reliability"} (the central isomorphism)

-   `isomorphism_preserves_failure_ordering`: Ordering preservation

-   `isomorphism_roundtrip`: Invertibility proof

-   `ordering_equivalence_exact`: Theorem [\[thm:approx-bound\]](#thm:approx-bound){reference-type="ref" reference="thm:approx-bound"} (exact ordering equivalence)

-   `linear_model_preserves_ordering`: Linear ordering support

-   `leverage_gap`: Theorem [\[thm:leverage-gap\]](#thm:leverage-gap){reference-type="ref" reference="thm:leverage-gap"}

-   `testable_modification_prediction`: Theorem [\[thm:testable-prediction\]](#thm:testable-prediction){reference-type="ref" reference="thm:testable-prediction"}

-   `dof_ratio_predicts_error_ratio`: Corollary [\[cor:dof-ratio\]](#cor:dof-ratio){reference-type="ref" reference="cor:dof-ratio"}

-   `lower_dof_lower_errors`: Corollary [\[cor:dof-monotone\]](#cor:dof-monotone){reference-type="ref" reference="cor:dof-monotone"}

-   `expected_errors_from_linearity`: Theorem [\[thm:expected-errors\]](#thm:expected-errors){reference-type="ref" reference="thm:expected-errors"}

-   `ssot_minimal_errors`: SSOT minimality


# Main Theorems

We prove the core results connecting leverage to error probability and architectural optimality. The theoretical structure is:

1.  **DOF-Reliability Isomorphism** (Theorem [\[thm:dof-reliability\]](#thm:dof-reliability){reference-type="ref" reference="thm:dof-reliability"}): Maps architecture to reliability theory

2.  **Leverage-Error Tradeoff** (Theorem [\[thm:leverage-error\]](#thm:leverage-error){reference-type="ref" reference="thm:leverage-error"}): Connects leverage to error probability

3.  **Physical Edit-Energy Floor** (Theorem [\[thm:physical-energy-floor\]](#thm:physical-energy-floor){reference-type="ref" reference="thm:physical-energy-floor"}): DOF controls minimum edit-energy

4.  **Optimality Criterion** (Theorem [\[thm:optimal\]](#thm:optimal){reference-type="ref" reference="thm:optimal"}): Correctness in a fixed capability class

5.  **Composition Stability** (Theorem [\[thm:composition\]](#thm:composition){reference-type="ref" reference="thm:composition"}): Composition preserves leverage lower bounds

## Recap: DOF-Reliability Isomorphism

The core theoretical contribution (stated in Section 1.3) is that DOF maps formally to series system components. This enables all subsequent results by connecting software architecture to the mature mathematical framework of reliability theory.

**Key properties of the isomorphism:**

-   **Preserves ordering:** If $\text{DOF}(A_1) < \text{DOF}(A_2)$, then $P_{\text{error}}(A_1) < P_{\text{error}}(A_2)$

-   **Invertible:** An architecture can be reconstructed from its series system representation

-   **Compositional:** $\text{DOF}(A_1 \oplus A_2) = \text{DOF}(A_1) + \text{DOF}(A_2)$ (series systems combine)

## The Leverage Maximization Principle

Given the DOF-Reliability Isomorphism, the following is a *corollary*:

::: theorem
[]{#thm:leverage-max label="thm:leverage-max"} For any architectural decision with alternatives $A_1, \ldots, A_n$ meeting capability requirements, the optimal choice maximizes leverage: $$A^* = \arg\max_{A_i} L(A_i) = \arg\max_{A_i} \frac{|\text{Capabilities}(A_i)|}{\text{DOF}(A_i)}$$
:::

**Note:** This is *not* the central theorem---it is a consequence of the DOF-Reliability Isomorphism. The isomorphism is the deep result; "maximize leverage" is the actionable heuristic derived from it.

## Leverage-Error Tradeoff

::: theorem
[]{#thm:leverage-error label="thm:leverage-error"} For architectures $A_1, A_2$ with equal capabilities: $$\text{Cap}(A_1) = \text{Cap}(A_2) \wedge L(A_1) > L(A_2) \implies P_{\text{error}}(A_1) < P_{\text{error}}(A_2)$$
:::

::: proof
*Proof.* Given: $\text{Cap}(A_1) = \text{Cap}(A_2)$ and $L(A_1) > L(A_2)$.

Since $L(A) = |\text{Cap}(A)|/\text{DOF}(A)$ and capabilities are equal: $$\frac{|\text{Cap}(A_1)|}{\text{DOF}(A_1)} > \frac{|\text{Cap}(A_2)|}{\text{DOF}(A_2)}$$

With $|\text{Cap}(A_1)| = |\text{Cap}(A_2)|$: $$\frac{1}{\text{DOF}(A_1)} > \frac{1}{\text{DOF}(A_2)} \implies \text{DOF}(A_1) < \text{DOF}(A_2)$$

By Corollary [\[cor:dof-monotone\]](#cor:dof-monotone){reference-type="ref" reference="cor:dof-monotone"}: $$\text{DOF}(A_1) < \text{DOF}(A_2) \implies P_{\text{error}}(A_1) < P_{\text{error}}(A_2)$$ ◻
:::

**Corollary:** Maximizing leverage minimizes error probability (for fixed capabilities).

## Physical Edit-Energy Floor

::: theorem
[]{#thm:physical-energy-floor label="thm:physical-energy-floor"} Fix a physical edit model $\mathcal{M}$ with per-edit conversion constant $j_{\mathcal{M}}>0$. For any architecture $A$: $$E_{\min}(A;\mathcal{M}) = j_{\mathcal{M}}\cdot \mathrm{DOF}(A).$$ Hence $\mathrm{DOF}(A_1) < \mathrm{DOF}(A_2)$ implies $E_{\min}(A_1;\mathcal{M}) < E_{\min}(A_2;\mathcal{M})$.
:::

::: proof
*Proof.* In the mechanized model, modification complexity is definitionally $\mathrm{DOF}$. Multiplying by a positive per-edit conversion constant gives the lower bound and strict monotonicity in DOF. ◻
:::

::: corollary
[]{#cor:leverage-energy label="cor:leverage-energy"} For architectures $A_1,A_2$ with equal capabilities, if $L(A_1)>L(A_2)$ then $$E_{\min}(A_1;\mathcal{M}) < E_{\min}(A_2;\mathcal{M}),$$ and the induced energy gap is strictly positive.
:::

::: theorem
[]{#thm:physical-budget-boundary label="thm:physical-budget-boundary"} For physical model $\mathcal{M}$ and budget $B$, implementation feasibility is equivalent to clearing the floor: $$E_{\min}(A;\mathcal{M}) \le B \iff \text{feasible}(A,B,\mathcal{M}).$$ Hence $B < E_{\min}(A;\mathcal{M})$ implies infeasibility. Also, for fixed $B$ and equal capabilities, if $L(A_1)>L(A_2)$ and $A_2$ is feasible under $B$, then $A_1$ is feasible under $B$.
:::

::: corollary
[]{#cor:physical-assumption-necessity label="cor:physical-assumption-necessity"} The physical layer uses two explicit premises for no-go style infeasibility claims: positive per-edit conversion and an external budget bound. Dropping positivity admits a zero-floor countermodel. Dropping the external budget-bound premise blocks infeasibility conclusions because a feasible budget witness always exists.
:::

## Metaprogramming Dominance

::: theorem
[]{#thm:metaprog label="thm:metaprog"} Metaprogramming (single source with unbounded derivations) achieves unbounded leverage.
:::

::: proof
*Proof.* Let $M$ be metaprogramming architecture with:

-   Source $S$: single definition (DOF $= 1$)

-   Derivations: unlimited capabilities can be derived from $S$

As capabilities grow: $|\text{Cap}(M)| \to \infty$

Therefore: $$L(M) = \frac{|\text{Cap}(M)|}{\text{DOF}(M)} = \frac{|\text{Cap}(M)|}{1} \to \infty$$ ◻
:::

## Architectural Decision Criterion

::: theorem
[]{#thm:optimal label="thm:optimal"} Given requirements $R$, architecture $A^*$ is optimal in its capability class if and only if:

1.  $\text{Cap}(A^*) \supseteq R$ (feasibility)

2.  $\forall A'$ with $\text{Cap}(A') = \text{Cap}(A^*)$ and $\text{Cap}(A') \supseteq R$: $L(A^*) \geq L(A')$ (maximality in fixed capability class)
:::

::: proof
*Proof.* ($\Leftarrow$) Suppose $A^*$ satisfies (1) and (2). Then $A^*$ is feasible and has maximum leverage among feasible architectures in the same capability class. By Theorem [\[thm:leverage-error\]](#thm:leverage-error){reference-type="ref" reference="thm:leverage-error"}, this minimizes error probability in that class.

($\Rightarrow$) If (1) fails, $A^*$ is infeasible. If (2) fails, there exists $A'$ in the same capability class with $L(A') > L(A^*)$, so $P_{\text{error}}(A') < P_{\text{error}}(A^*)$ by Theorem [\[thm:leverage-error\]](#thm:leverage-error){reference-type="ref" reference="thm:leverage-error"}, contradicting optimality. ◻
:::

**Decision Procedure:**

1.  Enumerate candidate architectures $\{A_1, \ldots, A_n\}$

2.  Filter: Keep only $A_i$ with $\text{Cap}(A_i) \supseteq R$

3.  Optimize: Choose $A^* = \arg\max_i L(A_i)$

## Leverage Composition

::: theorem
[]{#thm:composition label="thm:composition"} For modular architecture $A = A_1 \oplus A_2$ with disjoint components:

1.  $\text{DOF}(A) = \text{DOF}(A_1) + \text{DOF}(A_2)$

2.  if $L(A_1)\ge 1$ and $L(A_2)\ge 1$, then $L(A)\ge 1$
:::

::: proof
*Proof.* (1) By Proposition [\[prop:dof-additive\]](#prop:dof-additive){reference-type="ref" reference="prop:dof-additive"}.

\(2\) If $L(A_i)\ge 1$, then $|\text{Cap}(A_i)|\ge \text{DOF}(A_i)$ for $i=1,2$. Summing both inequalities gives $$|\text{Cap}(A_1)|+|\text{Cap}(A_2)|\ge \text{DOF}(A_1)+\text{DOF}(A_2),$$ which is exactly $L(A)\ge 1$ under additive composition. ◻
:::

**Interpretation:** Composition preserves a baseline leverage floor under the stated assumptions.

::: remark
[]{#rem:composition-breaks-ssot label="rem:composition-breaks-ssot"} Theorem [\[thm:composition\]](#thm:composition){reference-type="ref" reference="thm:composition"} preserves leverage *floors*, but composing two SSOT architectures breaks SSOT: if $\mathrm{DOF}(A_1) = \mathrm{DOF}(A_2) = 1$, then $\mathrm{DOF}(A_1 \oplus A_2) = 2$. This is formalized as `compose_breaks_ssot` in `Leverage/BridgeToDQ.lean`. The composition tax is unavoidable: distributed systems consisting of $k$ independent SSOT components have $\mathrm{DOF} = k$, placing them in the coNP-hard regime (srank $= k > 1$) with mandatory thermodynamic cost per decision cycle.
:::

## Formalization

Main optimization theorems are formalized in `Leverage/Theorems.lean`; physical edit-energy theorems are formalized in `Leverage/Physical.lean`:

-   L_22638fcd: Theorem [\[thm:leverage-error\]](#thm:leverage-error){reference-type="ref" reference="thm:leverage-error"}

-   L_9dc717da and L_bc94b2f8: Theorem [\[thm:physical-energy-floor\]](#thm:physical-energy-floor){reference-type="ref" reference="thm:physical-energy-floor"}, Corollary [\[cor:leverage-energy\]](#cor:leverage-energy){reference-type="ref" reference="cor:leverage-energy"}

-   L_53bac39c, L_dd0fab2d, and L_e5602ce9: Theorem [\[thm:physical-budget-boundary\]](#thm:physical-budget-boundary){reference-type="ref" reference="thm:physical-budget-boundary"}, Corollary [\[cor:physical-assumption-necessity\]](#cor:physical-assumption-necessity){reference-type="ref" reference="cor:physical-assumption-necessity"}

-   L_b85b0db1: Theorem [\[thm:metaprog\]](#thm:metaprog){reference-type="ref" reference="thm:metaprog"}

-   L_bb990fcf and L_7254810e: Theorem [\[thm:optimal\]](#thm:optimal){reference-type="ref" reference="thm:optimal"}

-   L_a4e66dad, L_f7a7de2d, and L_0869dd64: Theorem [\[thm:composition\]](#thm:composition){reference-type="ref" reference="thm:composition"}

-   `Leverage/Physical.lean`: physical edit-energy floor theorems

## Cross-Paper Integration

The leverage framework provides the unifying theory for results proven in Papers 1 and 2:

::: theorem
[]{#thm:paper1-integration label="thm:paper1-integration"} Nominal typing dominance from Paper 1 is an instance of leverage maximization:

-   Nominal typing adds 4 B-dependent capabilities over duck typing

-   DOF remains fixed in the mechanized typing instance

-   Therefore nominal typing has strictly higher leverage
:::

::: theorem
[]{#thm:paper2-integration label="thm:paper2-integration"} SSOT dominance from Paper 2 is an instance of leverage maximization:

-   SSOT fixes DOF at 1 for a structural fact

-   Non-SSOT replication yields DOF $= n$ for the same fact

-   Therefore leverage improves by factor $n$
:::

These integration theorems are formalized in:

-   `Leverage/Typing.lean`

-   `Leverage/SSOT.lean`


# Five-Way Equivalence

This section establishes the central result of the pentalogy: five independent characterizations of the same architectural property (DOF = 1 / SSOT) derived from five distinct first-principles frameworks. All proofs are machine-checked in Lean 4.

## Framework 1: Engineering Optimization (Leverage)

::: formal
**Theorem 5.1 (Maximum Leverage).** For any architecture $A$ with $\text{Cap}(A) > 0$, $A$ achieves maximum leverage among architectures with equal capabilities if and only if $\text{DOF}(A) = 1$.

Formally: $L(A) = \max_{A': \text{Cap}(A')=\text{Cap}(A)} L(A') \iff \text{DOF}(A) = 1$.
:::

::: informal
An architecture has the highest possible capability-to-DOF ratio exactly when it has a single degree of freedom.
:::

**Proof.**

-   (Forward) If $\text{DOF}(A) = 1$, then $L(A) = |\text{Cap}(A)|/1 = |\text{Cap}(A)|$. Any $A'$ with same capabilities has $\text{DOF}(A') \geq 1$, so $L(A') \leq |\text{Cap}(A)| = L(A)$.

-   (Backward) If $A$ has maximum leverage but $\text{DOF}(A) > 1$, construct $A'$ with $\text{DOF}(A') = 1$ and same capabilities. Then $L(A') = |\text{Cap}(A)| > |\text{Cap}(A)|/\text{DOF}(A) = L(A)$, contradiction.

## Framework 2: Architectural Epistemic Coherence (Paper 2)

::: formal
**Theorem 5.2 (Coherence).** An architecture satisfies the Single Source of Truth property if and only if $\text{DOF}(A) = 1$.

Formally: $\text{SSOT}(A) \iff \text{DOF}(A) = 1$.
:::

::: informal
Epistemic coherence (one source of truth per structural fact) is equivalent to having a single degree of freedom.
:::

This is the DOF = 1 characterization from Paper 2's coherence theorem.

## Framework 3: Information-Theoretic Structural Rank (Paper 4)

::: formal
**Theorem 5.3 (DOF-Structural Rank Isomorphism).** For any architecture $A$, let $\text{canonicalDP}(n)$ be the canonical decision problem with $n$ boolean coordinates. Then: $$\text{srank}(\text{canonicalDP}(\text{DOF}(A))) = \text{DOF}(A)$$
:::

::: informal
The structural rank (number of relevant decision coordinates) equals the degrees of freedom. The canonical encoding uses: states as $n$ boolean coordinates, actions as either querying a coordinate or falling back, and utilities that reward correct coordinate identification.
:::

The canonical encoding is:

-   States: $\text{Fin } n \to \text{Bool}$ ($n$ binary coordinates)

-   Actions: $\text{Fin } n \oplus \text{Unit}$ (query coordinate $i$, or fallback)

-   Utility: $u(\text{inl } i, s) = 2$ if $s(i) = \text{true}$, else $0$; $u(\text{inr } \(), s) = 1$

::: formal
**Corollary 5.4.** DOF $= 1$ if and only if srank $= 1$.

Formally: $\text{DOF}(A) = 1 \iff \text{srank}(\text{canonicalDP}(\text{DOF}(A))) = 1$.
:::

::: informal
An architecture has a single degree of freedom exactly when its canonical decision problem has minimal structural rank.
:::

## Framework 4: Computational Complexity (Tractability)

::: formal
**Theorem 5.5 (Tractability Boundary).** For the canonical decision problem with $n$ coordinates:

1.  If $n = 1$ (srank $= 1$), sufficiency checking is in P (polynomial time).

2.  If $n > 1$ (srank $> 1$), sufficiency checking is coNP-hard.
:::

::: informal
When the structural rank is 1, determining whether current information suffices for an optimal decision is computationally tractable. When the structural rank exceeds 1, the same problem is computationally intractable (coNP-hard).
:::

This connects the architectural property (DOF = 1) to computational feasibility of decision-making.

::: formal
**Corollary 5.6.** DOF $= 1$ (SSOT) is the unique architecture class for which sufficiency checking is tractable.
:::

::: informal
Among architectures, only those with a single degree of freedom admit tractable sufficiency checking.
:::

## Framework 5: Thermodynamic Selection (Statistical Physics)

::: formal
**Theorem 5.7 (Thermodynamic Selection).** Let $M$ be a thermodynamic model with Landauer calibration. For any architecture $A$ with DOF $> 1$:

1.  There exist decision instances where sufficiency checking requires $\Omega(2^{\text{DOF}})$ logical operations.

2.  Under P $\neq$ coNP, no polynomial-time sufficiency certification exists for these instances.

3.  Under the Landauer bound, each sufficiency-check cycle incurs mandatory positive energy cost.

For DOF $= 1$, the energy lower bound is zero.
:::

::: informal
Architectures with more than one degree of freedom necessarily incur thermodynamic costs per decision cycle due to the computational complexity of sufficiency checking. Architectures with exactly one degree of freedom have zero mandatory thermodynamic cost.
:::

Physical assumptions:

-   Positive per-edit conversion constant ($j_{\mathcal{M}} > 0$) --- cf. Theorem [\[cor:leverage-energy\]](#cor:leverage-energy){reference-type="ref" reference="cor:leverage-energy"} (L_9c6279a3, L_ebcd21af)

-   External budget bound --- cf. Theorem [\[cor:physical-assumption-necessity\]](#cor:physical-assumption-necessity){reference-type="ref" reference="cor:physical-assumption-necessity"} (L_a2e95cfd, L_f3216891, L_e0961ce8, L_1fb0826b)

-   P $\neq$ coNP (standard complexity assumption)

-   Landauer calibration ($k_B T \ln 2$ joules per bit)

Physical edit-energy floor from Section 4.3 is a special case: DOF controls minimum edit-energy, and higher leverage implies lower energy in a fixed capability class (Theorem [\[thm:physical-energy-floor\]](#thm:physical-energy-floor){reference-type="ref" reference="thm:physical-energy-floor"}, L_515d1d9d, L_5b347895, L_05a51b10).

## The Five-Way Equivalence

::: formal
**Theorem 5.8 (Five-Way Equivalence).** For any architecture $A$ with $\text{Cap}(A) > 0$, the following are equivalent: $$\text{DOF}(A) = 1 \iff \text{srank}(A) = 1 \iff \text{max leverage} \iff \text{tractable sufficiency} \iff \text{zero thermodynamic cost}$$
:::

::: informal
Five independent scientific frameworks---engineering optimization, epistemic coherence, information geometry, computational complexity, and statistical physics---all select the same architectural property: having exactly one degree of freedom.
:::

::: center
  **Domain**                 **Characterization of DOF $= 1$**
  -------------------------- -----------------------------------
  Engineering Optimization   Maximum leverage
  Architectural Epistemic    Single Source of Truth
  Information Geometry       Structural rank $= 1$
  Computational Complexity   Tractable sufficiency checking
  Statistical Physics        Zero thermodynamic cost per cycle
:::

**Proof.** The equivalence follows from Theorems 5.1-5.7:

1.  $\text{DOF} = 1 \iff \text{max leverage}$: Theorem 5.1 (L_ad7ca324, L_0c281f80)

2.  $\text{DOF} = 1 \iff \text{SSOT}$: Theorem 5.2 (Paper 2)

3.  $\text{DOF} = \text{srank}$: Theorem 5.3, so $\text{DOF} = 1 \iff \text{srank} = 1$

4.  $\text{srank} = 1 \iff \text{tractable sufficiency}$: Theorem 5.5 (Paper 4)

5.  $\text{DOF} > 1 \iff \text{positive thermodynamic cost}$: Theorem 5.7, so $\text{DOF} = 1 \iff \text{zero cost}$

The transitivity of logical equivalence gives the five-way equivalence.

::: formal
**Corollary 5.9 (Uniqueness).** The canonical encoding (states as $n$ boolean coordinates, actions as coordinate queries or fallback, utilities rewarding correct identification) is the unique decision structure that simultaneously satisfies all five characterizations.
:::

::: informal
The boolean-coordinate encoding is the unique structure that is simultaneously the leverage optimum, the epistemic coherence condition, the minimum-rank decision structure, the tractability boundary, and the thermodynamic ground state.
:::

**Proof.** Each characterization selects exactly one structure:

-   Maximum leverage requires DOF = 1, forcing a single coordinate.

-   SSOT requires a single source, forcing the same.

-   Structural rank = 1 requires exactly one relevant coordinate.

-   Tractability requires srank = 1, the same.

-   Zero thermodynamic cost requires DOF = 1, the same.

All five requirements converge to the same canonical encoding.

## Formalization

The following Lean 4 proofs establish the connections:

-   `Leverage/Foundations.lean`:

    -   `ssot_max_leverage` (L_ad7ca324, L_0c281f80): DOF $= 1 \to$ max leverage

    -   `max_leverage_forces_dof_one`: max leverage $\to$ DOF $= 1$

    -   `dof_one_iff_max_leverage`: biconditional

-   `Leverage/BridgeToDQ.lean`:

    -   `dof_eq_srank`: DOF $=$ srank

    -   `ssot_srank_one`: DOF $= 1 \to$ srank $= 1$

    -   `incoherent_srank_gt_one`: DOF $> 1 \to$ srank $> 1$

    -   `thermodynamic_selection`: DOF $> 1 \to$ mandatory energy

    -   `max_coherence_forces_tractability`: max leverage $\to$ tractable

-   `DecisionQuotient/Tractability/StructuralRank.lean`: srank $= 1 \to$ P, srank $> 1 \to$ coNP-hard (Paper 4)

-   `DecisionQuotient/ThermodynamicLift.lean`: energy lower bounds under Landauer calibration (Paper 4)

The cross-paper dependency chain is live: Paper 3 $\to$ Paper 4 $\to$ Mathlib.

## Relation to Prior Sections

This section subsumes and extends Section 4's results:

-   Theorem 4.1 (Leverage-Error Tradeoff, L_5af424e9) is a consequence of the equivalence between leverage and DOF

-   Theorem 4.2 (Modification Complexity Gap, L_45cc4f88) follows from DOF $= 1$ minimizing modification cost

-   Theorem 4.3 (Optimal Architecture, L_a42f986c, L_28e01ed8) is strengthened: the optimal architecture is now characterized by five independent properties

-   Theorem 4.4 (Metaprogramming Dominance, L_c022ff39, L_5250a1d9) is a special case: unbounded derivations from a single source achieve DOF $= 1$

## Open Conjectures

The five-way equivalence is proved under two hypotheses that we believe are removable: the complexity-theoretic assumption P $\neq$ coNP (used in Theorem 5.7), and the existential form of the energy lower bound (which gives no closed-form constant). Three open conjectures would strengthen the result.

::: conjecture
[]{#conj:unconditional-thermo label="conj:unconditional-thermo"} Theorem 5.7 holds without the P $\neq$ coNP assumption: for any architecture $A$ with $\mathrm{DOF}(A) > 1$, every decision cycle incurs a mandatory positive thermodynamic cost under Landauer calibration, *unconditionally*.

Formally: there exists a computable function $c : \mathbb{N} \to \mathbb{R}_{>0}$ such that $$\forall A.\; \mathrm{DOF}(A) > 1 \implies \text{energy per cycle} \geq c(\mathrm{DOF}(A)).$$ If proved, the five-way equivalence reduces entirely to physical necessities with no complexity-theoretic hypothesis.
:::

::: conjecture
[]{#conj:wolpert-bound label="conj:wolpert-bound"} The thermodynamic cost scales linearly with structural rank with an explicit Landauer constant. Specifically, let $\beta = 1/(k_B T)$ be the inverse temperature. Then for any architecture $A$: $$\text{energy per decision cycle} \geq \mathrm{srank}(A) \cdot k_B T \ln 2.$$ This would give a closed-form, quantitative version of Conjecture [\[conj:unconditional-thermo\]](#conj:unconditional-thermo){reference-type="ref" reference="conj:unconditional-thermo"}, replacing the existential witness with a tight bound derivable from first physical principles (Landauer's principle applied to each relevant coordinate). The bound would be tight at $\mathrm{srank} = 1$ (DOF $= 1$), where it predicts zero mandatory cost---consistent with Theorem 5.7's zero thermodynamic cost for DOF $=1$ architectures.

Evidence: Wolpert and Kolchinsky [@wolpert2019stochastic] prove thermodynamic cost bounds for multi-memory systems that scale with the number of relevant variables. The conjecture imports this result into the architectural setting via the $\mathrm{DOF} = \mathrm{srank}$ identity (Theorem 5.3).
:::

::: conjecture
[]{#conj:england label="conj:england"} Single-source architectures (DOF $= 1$) that generate $k$ derived instances are analogous to self-replicating systems in non-equilibrium thermodynamics. England's inequality [@england2013statistical] bounds the entropy production of self-replicating systems from below by a function of replication fidelity. We conjecture the following architectural analog:

Let $A_{\text{SSOT}}$ be a DOF $= 1$ architecture generating $k$ derived instances, and $A_{\text{rep}}$ a DOF $= k$ architecture maintaining $k$ independent copies. Then: $$\Delta S(A_{\text{SSOT}}) \leq \Delta S(A_{\text{rep}}) - k_B \ln k,$$ where $\Delta S$ denotes total entropy production per update cycle. This would formalize the intuition that SSOT architectures are thermodynamically preferred by at least $k_B \ln k$ per update---a strictly increasing advantage as the number of derivations grows.

The conjecture is consistent with the zero thermodynamic cost for DOF $= 1$ in Theorem 5.7, and would give it a quantitative non-equilibrium interpretation.
:::

**Significance.** If all three conjectures are proved, the five-way equivalence becomes a purely physical theorem: DOF $= 1$ is selected by thermodynamic necessity, complexity collapses to tractability as a consequence, and the energy advantage is quantified by a closed-form Landauer formula. The engineering optimization (leverage maximization) would then be derivable from statistical physics alone, with no combinatorial or epistemic axioms.


# Instances

We demonstrate that the leverage framework unifies prior results and applies to diverse architectural decisions.

## Instance 1: Single Source of Truth (SSOT)

We previously formalized the DRY principle, proving that Python uniquely provides SSOT for structural facts via definition-time hooks and introspection. Here we show SSOT is an instance of leverage maximization.

### Prior Result

**Published Theorem:** A language enables SSOT for structural facts if and only if it provides (1) definition-time hooks AND (2) introspectable derivation results. Python is the only mainstream language satisfying both requirements.

**Modification Complexity:** For structural fact $F$ with $n$ use sites:

-   SSOT: $M(\text{change } F) = 1$ (modify source, derivations update automatically)

-   Non-SSOT: $M(\text{change } F) = n$ (modify each use site independently)

### Leverage Perspective

::: definition
Architecture $A_{\text{SSOT}}$ for structural fact $F$ has:

-   Single source $S$ defining $F$

-   Derived use sites updated automatically from $S$

-   DOF $= 1$ (only $S$ is independently modifiable)
:::

::: definition
Architecture $A_{\text{non-SSOT}}$ for structural fact $F$ with $n$ use sites has:

-   $n$ independent definitions (copied or manually synchronized)

-   DOF $= n$ (each definition independently modifiable)
:::

::: theorem
[]{#thm:ssot-leverage label="thm:ssot-leverage"} For structural fact with $n$ use sites: $$\frac{L(A_{\text{SSOT}})}{L(A_{\text{non-SSOT}})} = n$$
:::

::: proof
*Proof.* Both architectures provide same capabilities: $|\text{Cap}(A_{\text{SSOT}})| = |\text{Cap}(A_{\text{non-SSOT}})| = c$.

DOF: $$\begin{aligned}
\text{DOF}(A_{\text{SSOT}}) &= 1 \\
\text{DOF}(A_{\text{non-SSOT}}) &= n
\end{aligned}$$

Leverage: $$\begin{aligned}
L(A_{\text{SSOT}}) &= c/1 = c \\
L(A_{\text{non-SSOT}}) &= c/n
\end{aligned}$$

Ratio: $$\frac{L(A_{\text{SSOT}})}{L(A_{\text{non-SSOT}})} = \frac{c}{c/n} = n$$ ◻
:::

::: corollary
As use sites grow ($n \to \infty$), leverage advantage grows unbounded.
:::

::: corollary
For small $p$: $$\frac{P_{\text{error}}(A_{\text{non-SSOT}})}{P_{\text{error}}(A_{\text{SSOT}})} \approx n$$
:::

**Connection to Prior Work:** Our published Theorem 6.3 (Unbounded Complexity Gap) showed $M(\text{SSOT}) = O(1)$ vs $M(\text{non-SSOT}) = \Omega(n)$. Theorem [\[thm:ssot-leverage\]](#thm:ssot-leverage){reference-type="ref" reference="thm:ssot-leverage"} provides the leverage perspective: SSOT achieves $n$-times better leverage.

## Instance 2: Nominal Typing Dominance

We previously proved nominal typing strictly dominates structural and duck typing for OO systems with inheritance. Here we show this is an instance of leverage maximization.

### Prior Result

**Published Theorems:**

1.  Theorem 3.13 (Provenance Impossibility): No shape discipline can compute provenance

2.  Theorem 3.19 (Capability Gap): Gap = B-dependent queries = {provenance, identity, enumeration, conflict resolution}

3.  Theorem 3.5 (Strict Dominance): Nominal strictly dominates duck typing

### Leverage Perspective

::: definition
A typing discipline $D$ is an architecture where:

-   Components = type checker, runtime dispatch, introspection APIs

-   Capabilities = queries answerable by the discipline
:::

**Duck Typing:** Uses only Shape axis ($S$: methods, attributes)

-   Capabilities: Shape checking ("Does object have method $m$?")

-   Cannot answer: provenance, identity, enumeration, conflict resolution

**Nominal Typing:** Uses Name + Bases + Shape axes ($N + B + S$)

-   Capabilities: All duck capabilities PLUS 4 B-dependent capabilities

-   Can answer: "Which type provided method $m$?" (provenance), "Is this exactly type $T$?" (identity), "List all subtypes of $T$" (enumeration), "Which method wins in diamond?" (conflict)

::: observation
Nominal and duck typing have similar implementation complexity (both are typing disciplines with similar runtime overhead).
:::

::: theorem
[]{#thm:nominal-leverage label="thm:nominal-leverage"} $$L(\text{Nominal}) > L(\text{Duck})$$
:::

::: proof
*Proof.* Let $c_{\text{duck}}  = |\text{Cap}(\text{Duck})|$ and $c_{\text{nominal}} = |\text{Cap}(\text{Nominal})|$.

By Theorem 3.19 (published): $$c_{\text{nominal}} = c_{\text{duck}} + 4$$

By Observation (similar DOF): $$\text{DOF}(\text{Nominal}) \approx \text{DOF}(\text{Duck}) = d$$

Therefore: $$L(\text{Nominal}) = \frac{c_{\text{duck}} + 4}{d} > \frac{c_{\text{duck}}}{d} = L(\text{Duck})$$ ◻
:::

**Connection to Prior Work:** Our published Theorem 3.5 (Strict Dominance) showed nominal typing provides strictly more capabilities for same DOF cost. Theorem [\[thm:nominal-leverage\]](#thm:nominal-leverage){reference-type="ref" reference="thm:nominal-leverage"} provides the leverage formulation.

## Instance 3: Microservices Architecture

Should a system use microservices or a monolith? How many services are optimal? The leverage framework provides answers. This architectural style, popularized by Fowler and Lewis [@fowler2014microservices], traces its roots to the Unix philosophy of "doing one thing well" [@pike1984program].

### Architecture Comparison

**Monolith:**

-   Components: Single deployment unit

-   DOF $= 1$

-   Capabilities: Basic functionality, simple deployment

**$n$ Microservices:**

-   Components: $n$ independent services

-   DOF $= n$ (each service independently deployable/modifiable)

-   Additional Capabilities: Independent scaling, independent deployment, fault isolation, team autonomy, polyglot persistence [@fowler2014microservices]

### Leverage Analysis

Let $c_0$ = capabilities provided by monolith.

Let $\Delta c = 5$ denote the additional capabilities from microservices: independent scaling, independent deployment, fault isolation, team autonomy, and polyglot persistence.

**Leverage:** $$\begin{aligned}
L(\text{Monolith}) &= c_0 / 1 = c_0 \\
L(n \text{ Microservices}) &= (c_0 + \Delta c) / n = (c_0 + 5) / n
\end{aligned}$$

**Break-even Point:** $$L(\text{Microservices}) \geq L(\text{Monolith}) \iff \frac{c_0 + 5}{n} \geq c_0 \iff n \leq 1 + \frac{5}{c_0}$$

**Interpretation:** If base capabilities $c_0 = 5$, then $n \leq 2$ services is optimal. For $c_0 = 20$, up to $n = 1.25$ (i.e., monolith still better). Microservices justified only when additional capabilities significantly outweigh DOF cost.

## Instance 4: REST API Design

Generic endpoints vs specific endpoints: a leverage tradeoff.

### Architecture Comparison

**Specific Endpoints:** One endpoint per use case

-   Example: `GET /users`, `GET /posts`, `GET /comments`, \...

-   For $n$ use cases: DOF $= n$

-   Capabilities: Serve $n$ use cases

**Generic Endpoint:** Single parameterized endpoint

-   Example: `GET /resources/:type/:id`

-   DOF $= 1$

-   Capabilities: Serve $n$ use cases (same as specific)

### Leverage Analysis

$$\begin{aligned}
L(\text{Generic}) &= n / 1 = n \\
L(\text{Specific}) &= n / n = 1
\end{aligned}$$

**Advantage:** $L(\text{Generic}) / L(\text{Specific}) = n$

**Tradeoff:** Generic endpoint has higher leverage but may sacrifice:

-   Type safety (dynamic routing)

-   Specific validation per resource

-   Tailored response formats

**Decision Rule:** Use generic if $n > k$ where $k$ is complexity threshold (typically $k \approx 3$--$5$).

## Instance 5: Configuration Systems

Convention over configuration (CoC) reduces developer decisions and preserves flexibility [@hansson2005rails]. In this framework it is leverage maximization via defaults.

### Architecture Comparison

**Explicit Configuration:** Must set all $m$ parameters

-   DOF $= m$ (each parameter independently set)

-   Capabilities: Configure $m$ aspects

**Convention over Configuration:** Provide defaults, override only $k$ parameters

-   DOF $= k$ where $k \ll m$

-   Capabilities: Configure same $m$ aspects (defaults handle rest)

**Example (Rails vs Java EE):**

-   Rails: 5 config parameters (convention for rest)

-   Java EE: 50 config parameters (explicit for all)

### Leverage Analysis

$$\begin{aligned}
L(\text{Convention}) &= m / k \\
L(\text{Explicit}) &= m / m = 1
\end{aligned}$$

**Advantage:** $L(\text{Convention}) / L(\text{Explicit}) = m/k$

For Rails example: $m/k = 50/5 = 10$ (10$\times$ leverage improvement).

## Instance 6: Database Schema Normalization

Normalization eliminates redundancy, maximizing leverage. This concept, introduced by Codd [@codd1970relational], is the foundation of relational database design [@date2003introduction].

### Architecture Comparison

Consider customer address stored in database:

**Denormalized (Address in 3 tables):**

-   `Users` table: address columns

-   `Orders` table: shipping address columns

-   `Invoices` table: billing address columns

-   DOF $= 3$ (address stored 3 times)

**Normalized (Address in 1 table):**

-   `Addresses` table: single source

-   Foreign keys from `Users`, `Orders`, `Invoices`

-   DOF $= 1$ (address stored once)

### Leverage Analysis

Both provide same capability: store/retrieve addresses.

$$\begin{aligned}
L(\text{Normalized}) &= c / 1 = c \\
L(\text{Denormalized}) &= c / 3
\end{aligned}$$

**Advantage:** $L(\text{Normalized}) / L(\text{Denormalized}) = 3$

**Modification Complexity:**

-   Change address format: Normalized $M = 1$, Denormalized $M = 3$

-   Error probability: $P_{\text{denorm}} = 3p$ vs $P_{\text{norm}} = p$

**Tradeoff:** Normalization increases leverage but may sacrifice query performance (joins required).

## Summary of Instances

::: center
  **Instance**        **High Leverage**          **Low Leverage**        **Ratio**
  ---------------- ------------------------ -------------------------- -------------
  SSOT                     DOF = 1                  DOF = $n$               $n$
  Nominal Typing     $c+4$ caps, DOF $d$        $c$ caps, DOF $d$        $(c+4)/c$
  Microservices       Monolith (DOF = 1)     $n$ services (DOF = $n$)   $n/(c_0+5)$
  REST API            Generic (DOF = 1)        Specific (DOF = $n$)         $n$
  Configuration     Convention (DOF = $k$)     Explicit (DOF = $m$)        $m/k$
  Database           Normalized (DOF = 1)    Denormalized (DOF = $n$)       $n$
:::

**Pattern:** High leverage architectures achieve $n$-fold improvement where $n$ is the consolidation factor (use sites, services, endpoints, parameters, or redundant storage).


# Practical Demonstration

We demonstrate the leverage framework by showing how DOF collapse patterns manifest in OpenHCS, a production 45K LoC Python bioimage analysis platform. This section presents qualitative before/after examples illustrating the leverage archetypes, with PR #44 providing a publicly verifiable anchor.

## The Leverage Mechanism

For a before/after pair $A_{\text{pre}}, A_{\text{post}}$, the **structural leverage factor** is: $$\rho := \frac{\mathrm{DOF}(A_{\text{pre}})}{\mathrm{DOF}(A_{\text{post}})}.$$ If capabilities are preserved, leverage scales exactly by $\rho$. The key insight: when $\mathrm{DOF}(A_{\text{post}}) = 1$, we achieve $\rho = n$ where $n$ is the original DOF count.

#### What counts as a DOF?

Independent *definition loci*: manual registration sites, independent override parameters, separately defined endpoints/handlers/rules, duplicated schema/format definitions. The unit is "how many places can drift apart," not lines of code.

## Verifiable Example: PR #44 (Contract Enforcement)

PR #44 ("UI Anti-Duck-Typing Refactor") in the OpenHCS repository provides a publicly verifiable demonstration of DOF collapse:

**Before (duck typing):** The `ParameterFormManager` class used scattered `hasattr()` checks throughout the codebase. Each dispatch point was an independent DOF---a location that could drift, contain typos, or miss updates when widget interfaces changed.

**After (nominal ABC):** A single `AbstractFormWidget` ABC defines the contract. All dispatch points collapsed to one definition site. The ABC provides fail-loud validation at class definition time rather than fail-silent behavior at runtime.

**Leverage interpretation:** DOF collapsed from $n$ scattered dispatch points to 1 centralized ABC. By Theorem 3.1, this achieves $\rho = n$ leverage improvement. The specific value of $n$ is verifiable by inspecting the PR diff.

## Leverage Archetypes

The framework identifies recurring patterns where DOF collapse occurs:

### Archetype 1: SSOT (Single Source of Truth)

**Pattern:** Scattered definitions $\to$ single authoritative source.

**Mechanism:** Metaclass auto-registration, decorator-based derivation, or introspection-driven generation eliminates manual synchronization.

**Before:** Define class + register in dispatch table (2 loci per type). **After:** Define class; metaclass auto-registers (1 locus per type).

**Leverage:** $\rho = 2$ per type; compounds across $n$ types.

### Archetype 2: Convention over Configuration

**Pattern:** Explicit parameters $\to$ sensible defaults with override.

**Mechanism:** Framework provides defaults; users override only non-standard values.

**Before:** Specify all $m$ configuration parameters explicitly. **After:** Override only $k \ll m$ parameters; defaults handle rest.

**Leverage:** $\rho = m/k$.

### Archetype 3: Generic Abstraction

**Pattern:** Specific implementations $\to$ parameterized generic.

**Mechanism:** Factor common structure into generic endpoint/handler with parameters for variation.

**Before:** $n$ specific endpoints with duplicated logic. **After:** 1 generic endpoint with $n$ parameter instantiations.

**Leverage:** $\rho = n$.

### Archetype 4: Centralization

**Pattern:** Scattered cross-cutting concerns $\to$ centralized handler.

**Mechanism:** Middleware, decorators, or aspect-oriented patterns consolidate error handling, logging, authentication, etc.

**Before:** Each call site handles concern independently. **After:** Central handler; call sites delegate.

**Leverage:** $\rho = n$ where $n$ is number of call sites.

## Summary

The leverage framework identifies a common mechanism across diverse refactoring patterns: DOF collapse yields proportional leverage improvement. Whether the pattern is SSOT, convention-over-configuration, generic abstraction, or centralization, the mathematical structure is identical: reduce DOF while preserving capabilities.

PR #44 provides a verifiable anchor demonstrating this mechanism in practice. The qualitative value lies not in aggregate statistics but in the *mechanism*: once understood, the pattern applies wherever scattered definitions can be consolidated.


# Related Work

## Software Architecture Metrics

**Coupling and Cohesion [@stevens1974structured]:** Introduced coupling (inter-module dependencies) and cohesion (intra-module relatedness). Recommend high cohesion, low coupling.

**Difference:** Our framework is capability-aware. High cohesion correlates with high leverage (focused capabilities per module), but we formalize the connection to error probability.

**Cyclomatic Complexity [@mccabe1976complexity]:** Counts decision points in code. Higher values are commonly used as a risk indicator, though empirical studies on defect correlation show mixed results.

**Difference:** Complexity measures local control flow; leverage measures global architectural DOF. Orthogonal concerns.

## Design Patterns

**Gang of Four [@gamma1994design]:** Catalogued 23 design patterns (Singleton, Factory, Observer, etc.). Patterns codify best practices but lack formal justification.

**Connection:** Many patterns maximize leverage:

-   **Factory Pattern:** Centralizes object creation (DOF $= 1$ for creation logic)

-   **Strategy Pattern:** Encapsulates algorithms (DOF $= 1$ per strategy family)

-   **Template Method:** Defines algorithm skeleton (DOF $= 1$ for structure)

Our framework explains *why* these patterns work: they maximize leverage.

## Technical Debt

**Cunningham [@cunningham1992wycash]:** Introduced technical debt metaphor. Poor design creates "debt" that must be "repaid" later.

**Connection:** Low leverage = high technical debt. Scattered DOF (non-SSOT, denormalized schemas, specific endpoints) create debt. High leverage architectures minimize debt.

## Formal Methods in Software Architecture

**Architecture Description Languages (ADLs):** Wright [@allen1997formal], ACME [@garlan1997acme], Aesop [@garlan1994exploiting]. Formalize architecture structure but not decision-making. See also Shaw and Garlan [@shaw1996software].

**Difference:** ADLs describe architectures; our framework prescribes optimal architectures via leverage maximization.

**ATAM and CBAM:** Architecture Tradeoff Analysis Method [@kazman2000atam] and Cost Benefit Analysis Method [@bachmann2000cbam]. Evaluate architectures against quality attributes (performance, modifiability, security). See also Bass et al. [@bass2012software].

**Difference:** ATAM is qualitative; our framework provides quantitative optimization criterion (maximize $L$).

**Necessity Specifications:** Mackay et al. [@mackay2022necessity] formalize *necessity specifications*---robustness guarantees that modules do only what their specification requires, even under adversarial clients. Soundness is mechanized in Coq.

**Connection:** Necessity specifications address *behavioral minimality*: modules commit to no more behavior than required. Our framework addresses *structural minimality*: architectures commit to no more DOF than required. Both derive minimal commitments from requirements and prove sufficiency.

## Software Metrics Research

**Chidamber-Kemerer Metrics [@chidamber1994metrics]:** Object-oriented metrics (WMC, DIT, NOC, CBO, RFC, LCOM). Empirical validation studies [@basili1996comparing] found these metrics correlate with external quality attributes.

**Connection:** Metrics like CBO (Coupling Between Objects) and LCOM (Lack of Cohesion) correlate with DOF. High CBO $\implies$ high DOF. Our framework provides theoretical foundation.

## Metaprogramming and Reflection

**Reflection [@maes1987concepts]:** Languages with reflection enable introspection and intercession. Essential for metaprogramming.

**Connection:** Reflection enables high leverage (SSOT). Our prior work showed Python's definition-time hooks + introspection uniquely enable SSOT for structural facts.

**Metaclasses [@bobrow1986commonloops; @kiczales1991amop]:** Early metaobject and metaclass machinery formalized in CommonLoops; the Metaobject Protocol codified in Kiczales et al.'s AMOP. Enable metaprogramming patterns.

**Application:** Metaclasses are high-leverage mechanism (DOF $= 1$ for class structure, unlimited derivations).


# Extension: Weighted Leverage {#weighted-leverage}

The basic leverage framework treats all errors equally. In practice, different decisions carry different consequences. This section extends our framework with *weighted leverage* to capture heterogeneous error severity.

## Weighted Decision Framework

::: definition
A **weighted decision** extends an architecture with:

-   **Importance weight** $w \in \mathbb{N}^+$: the relative severity of errors in this decision

-   **Risk-adjusted DOF**: $\text{DOF}_w = \text{DOF} \times w$
:::

The key insight is that a decision with importance weight $w$ carries $w$ times the error consequence of a unit-weight decision. This leads to:

::: definition
$$L_w = \frac{\text{Capabilities} \times w}{\text{DOF}_w} = \frac{\text{Capabilities}}{\text{DOF}}$$
:::

The cancellation is intentional: weighted leverage preserves comparison properties while enabling risk-adjusted optimization.

## Key Theorems

::: theorem
For any weighted decision $d$ with $\text{DOF} = 1$: $d$ is Pareto-optimal (not dominated by any alternative with higher weighted leverage).
:::

::: proof
*Proof.* Suppose $d$ has $\text{DOF} = 1$. For any $d'$ to dominate $d$, we would need $d'.\text{DOF} < 1$. But $\text{DOF} \geq 1$ by definition, so no such $d'$ exists. ◻
:::

::: theorem
$\forall a, b, c$: if $a$ has higher weighted leverage than $b$, and $b$ has higher weighted leverage than $c$, then $a$ has higher weighted leverage than $c$.
:::

::: proof
*Proof.* By algebraic manipulation of cross-multiplication inequalities. Formally verified in Lean (38-line proof). ◻
:::

## Practical Application: Feature Flags

Consider two approaches to feature toggle implementation:

**Low Leverage (Scattered Conditionals):**

-   DOF: One per feature $\times$ one per use site ($n \times m$)

-   Risk: Inconsistent behavior if any site is missed

-   Weight: High (user-facing inconsistency)

**High Leverage (Centralized Configuration):**

-   DOF: One per feature

-   Risk: Single source of truth eliminates inconsistency

-   Weight: Same importance, but $m\times$ fewer DOF

Weighted leverage ratio: $L_{\text{centralized}} / L_{\text{scattered}} = m$, the number of use sites.

## Connection to Main Theorems

The weighted framework preserves all results from Sections 3--5:

-   **Theorem 3.1 (Leverage-Error Tradeoff)**: Holds with weighted errors

-   **Theorem 3.2 (Metaprogramming Dominance)**: Weight amplifies the advantage

-   **Theorem 3.4 (Optimality)**: Weighted optimization finds risk-adjusted optima

-   **SSOT Dominance**: Weight $w$ makes $n \times w$ leverage advantage

All proofs verified in Lean: `Leverage/WeightedLeverage.lean` (348 lines, 0 sorry placeholders).


# Conclusion

## Methodology and Disclosure

**Role of LLMs in this work.** This paper was developed through human-AI collaboration. The author provided the core insight---that DOF $= 1$ is selected by five independent scientific frameworks---while large language models (Claude, GPT-4) served as implementation partners for formalization, proof drafting, and LaTeX generation.

The Lean 4 proofs (3691 lines, 0 `sorry` placeholders) were iteratively developed: the author specified theorems, the LLM proposed proof strategies, and the Lean compiler verified correctness. Machine-checked proofs are correct regardless of generation method.

**What the author contributed:** The five-way convergence insight, the identification of structural rank as the information-geometric coordinate of DOF, the thermodynamic selection theorem, the cross-paper dependency chain, the open conjectures, and the OpenHCS case study selection.

**What LLMs contributed:** LaTeX drafting, Lean tactic suggestions, prose refinement, and exploration of proof strategies.

::: center

----------------------------------------------------------------------------------------------------
:::

## Summary

The central result is the Five-Way Equivalence (Theorem 5.8): five independent scientific frameworks all characterize the single-source condition (DOF $= 1$).

::: center
  **Framework**              **DOF $= 1$ means**                                  **Source**
  -------------------------- ---------------------------------------------------- -------------
  Engineering optimization   Maximum leverage $L = |\mathrm{Cap}|/\mathrm{DOF}$   This paper
  Epistemic coherence        Single Source of Truth                               Paper 2
  Information geometry       Structural rank $= 1$                                Paper 4
  Computational complexity   Tractable sufficiency checking                       Paper 4
  Statistical physics        Zero thermodynamic cost per cycle                    Papers 3--4
:::

The engineering consequences (Theorems 1--6 from the prior conclusion) are corollaries: DOF--Reliability Isomorphism, Leverage--Error Tradeoff, Modification Complexity Gap, Physical Edit-Energy Floor, Budget Feasibility Boundary, and the Optimal Architecture decision procedure. All are machine-checked in Lean 4 with live cross-paper imports.

**What is new in Paper 3 relative to Papers 1 and 2:**

-   The convergence theorem itself---Papers 1 and 2 contain two of the five equivalences; this paper closes the chain.

-   The thermodynamic selection theorem (`thermodynamic_selection` in `BridgeToDQ.lean`): mandatory energy under Landauer calibration for DOF $> 1$.

-   The identification of structural rank as the information coordinate for DOF.

-   Three open conjectures that, if proved, reduce the equivalence to purely physical necessity.

## Open Problems

The following conjectures are within reach of the current formalization infrastructure.

**Conjecture 1 (Unconditional Thermodynamic Selection, Section [\[five-way-equivalence\]](#five-way-equivalence){reference-type="ref" reference="five-way-equivalence"}).** Remove the P $\neq$ coNP assumption from Theorem 5.7. Show directly that DOF $> 1$ architectures incur mandatory positive energy per decision cycle under Landauer calibration, without invoking computational hardness. Strategy: use Wolpert--Kolchinsky multi-memory bounds applied to architectures with srank $> 1$ (which equals DOF $> 1$ by Theorem 5.3).

**Conjecture 2 (Wolpert--Kolchinsky Quantitative Bound, Section [\[five-way-equivalence\]](#five-way-equivalence){reference-type="ref" reference="five-way-equivalence"}).** Prove a closed-form lower bound: energy per decision cycle $\geq \mathrm{srank}(A) \cdot k_B T \ln 2$. This quantifies the thermodynamic advantage of DOF $= 1$ architectures and gives a formula for the energy gap between architectural alternatives. The bound should be tight: at DOF $= 1$, it predicts zero mandatory cost (consistent with Theorem 5.7).

**Conjecture 3 (England Replication Inequality, Section [\[five-way-equivalence\]](#five-way-equivalence){reference-type="ref" reference="five-way-equivalence"}).** Prove a non-equilibrium analog of England's self-replication inequality for SSOT architectures. A DOF $= 1$ architecture generating $k$ derivations should satisfy $\Delta S(A_{\mathrm{SSOT}}) \leq \Delta S(A_{\mathrm{rep}}) - k_B \ln k$ relative to a DOF $= k$ replication architecture, with the advantage growing logarithmically in the number of derivations.

**Priority and method.** Conjecture 1 is the most important because it removes the conditional from the five-way equivalence. Conjectures 2 and 3 add quantitative content. All three are attackable via the existing Lean formalization: `ThermodynamicLift.lean` already contains the Landauer calibration infrastructure, and `StructuralRank.lean` proves the srank $=$ DOF identity needed to import Wolpert--Kolchinsky results.

## Decision Procedure

For practitioners, the five-way equivalence implies a principled architectural decision procedure.

Given requirements $R$, choose optimal architecture via:

1.  **Enumerate:** List candidate architectures $\{A_1, \ldots, A_n\}$

2.  **Filter:** Keep only $A_i$ with $\mathrm{Cap}(A_i) \supseteq R$

3.  **Compute:** Calculate $L(A_i) = |\mathrm{Cap}(A_i)|/\mathrm{DOF}(A_i)$ for each

4.  **Optimize:** Choose $A^* = \arg\max_i L(A_i)$

**Justification:** By the Five-Way Equivalence, $A^*$ simultaneously (a) maximizes leverage, (b) satisfies SSOT, (c) has minimum structural rank, (d) admits tractable sufficiency checking, and (e) minimizes thermodynamic cost. These are five independent validations of the same choice.

## Limitations

**1. Independence Assumption:** The probability model treats DOF-level errors as independent under the orthogonality assumptions from Paper 1. Real systems may have correlated failure modes not captured by the isomorphism.

**2. Constant Error Rate:** Assumes $p$ is uniform across components. Some components are more error-prone than others; a weighted version is future work.

**3. P $\neq$ coNP Hypothesis:** The thermodynamic selection theorem (Theorem 5.7) currently requires P $\neq$ coNP. This is standard and believed true; Conjecture 1 would remove it.

**4. Capability Quantification:** We count capabilities qualitatively. Some capabilities are more valuable; a weighted leverage extension $L = \sum w_i c_i / \mathrm{DOF}$ is natural but unformalized.

## Impact

**For Practitioners:** Five independent reasons to prefer DOF $= 1$ architectures. When choosing between alternatives, compute leverage and select maximum---but know that you are simultaneously satisfying epistemic coherence, minimizing structural rank, enabling tractable decision-making, and minimizing thermodynamic cost.

**For Researchers:** A convergence result connecting software architecture to information theory, computational complexity, and statistical physics. The five-way equivalence is the kind of result that appears in mature mathematical fields (e.g., equivalent characterizations of compactness, or equivalent formulations of the axiom of choice); its appearance in software architecture suggests the field has a deeper mathematical structure than previously recognized.

**For Physicists:** A formal setting in which Landauer's principle applies to software design decisions. The architectural ground state (DOF $= 1$) is the thermodynamic ground state. If the three conjectures are proved, software architecture becomes a branch of non-equilibrium statistical mechanics.

## Final Remarks

Software architecture has long relied on heuristics and experience. This paper provides formal foundations: *architectural quality is fundamentally about degrees of freedom*. The single-source condition is not an engineering preference---it is selected by five independent scientific frameworks as the unique optimum.

The three open conjectures mark the frontier. If Conjecture 1 is proved, the complexity-theoretic condition disappears and the result becomes physical. If Conjecture 2 is proved, a closed-form energy formula gives the thermodynamic cost of architectural decisions. If Conjecture 3 is proved, England's replication inequality applies to software systems and the entropy advantage of SSOT is quantified.

We invite the community to attack these conjectures using the existing Lean formalization infrastructure, and to apply the five-way framework to identify architectural ground states in other domains.


# Lean Proof Artifacts {#appendix-lean}

This appendix reports machine-check status and proof traceability directly from source and generated mapping artifacts.

## Verification Status

**Lean summary:** 3691 lines, 201 theorems/lemmas, 0 `sorry`, across 14 files.

::: center
  **File**                                  **Lines**   **Theorems/Lemmas**
  ---------------------------------------- ----------- ---------------------
  `LambdaDR.lean`                              343              24
  `Leverage.lean`                              115               0
  `Leverage/Foundations.lean`                  234              13
  `Leverage/Probability.lean`                  841              39
  `Leverage/Theorems.lean`                     303              20
  `Leverage/SSOT.lean`                         192              13
  `Leverage/Typing.lean`                       210              15
  `Leverage/Examples.lean`                     184               4
  `Leverage/WeightedLeverage.lean`             348              13
  `Leverage/BridgeToDQ.lean`                   277              17
  `Leverage/FiveWayEquivalence.lean`           149               7
  `Leverage/CrossPaperDependencies.lean`       332              22
  `lakefile.lean`                              19                0
  **Total**                                 **3691**          **201**
:::

Build command: `cd proofs && lake build`

## Claim Coverage Matrix

## Lean Handle Map

## Proof Hardness Index


  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  **Paper handle**                      **Status**   **Lean support**
  ------------------------------------- ------------ ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  `cor:dof-errors`                      Full         `L.architecture_axes_independent`, `L.error_independence_from_orthogonality`

  `cor:dof-monotone`                    Full         `L.lower_dof_lower_errors`

  `cor:dof-ratio`                       Full         `L.dof_ratio_predicts_error_ratio`

  `cor:leverage-energy`                 Full         `L.Physical.higher_leverage_same_caps_implies_lower_energy`, `L.Physical.positive_energy_gap_of_higher_leverage`

  `cor:linear-approx`                   Full         `L.bernoulli_justifies_linear_model`, `L.ordering_equivalence_exact`

  `cor:physical-assumption-necessity`   Full         `L.Physical.feasible_budget_exists`, `L.Physical.physical_assumption_necessity_witnesses`, `L.Physical.positive_floor_requires_positive_joules_assumption`, `L.Physical.zero_model_energy_is_zero`

  `prop:dof-additive`                   Full         `L.compose_dof`, `L.composition_dof_additive`

  `thm:approx-bound`                    Full         `L.linear_model_preserves_ordering`, `L.ordering_equivalence_exact`

  `thm:composition`                     Full         `L.composition_caps_additive`, `L.composition_dof_additive`, `L.composition_preserves_leverage_bound`

  `thm:dof-reliability`                 Full         `L.dof_reliability_isomorphism`, `L.isomorphism_preserves_failure_ordering`, `L.isomorphism_roundtrip`

  `thm:error-compound`                  Full         `L.correctness_probability`, `L.system_is_correct`

  `thm:error-independence`              Full         `L.error_independence_from_orthogonality`

  `thm:error-prob`                      Full         `L.error_probability_denom_pos`, `L.series_error_probability`

  `thm:expected-errors`                 Full         `L.expected_errors_from_linearity`, `L.expected_errors_linear`

  `thm:five-way`                        Unmapped     *(no derived Lean handle found)*

  `thm:leverage-error`                  Full         `L.leverage_error_tradeoff`

  `thm:leverage-gap`                    Full         `L.leverage_gap`

  `thm:leverage-max`                    Full         `L.leverage_caps_principle`, `L.leverage_maximization_principle`

  `thm:metaprog`                        Full         `L.metaprogramming_dominates`, `L.metaprogramming_unbounded_leverage`

  `thm:mod-bound`                       Full         `L.modification_eq_dof`

  `thm:nominal-leverage`                Full         `L.Typing.capability_gap`, `L.Typing.leverage_ratio`, `L.Typing.nominal_dominates_duck`

  `thm:optimal`                         Full         `L.max_leverage_is_optimal`, `L.optimal_minimizes_error`

  `thm:paper1-integration`              Full         `L.Typing.nominal_dominates_duck`, `L.Typing.paper1_is_leverage_instance`

  `thm:paper2-integration`              Full         `L.SSOT.paper2_is_leverage_instance`, `L.SSOT.ssot_leverage_dominance`

  `thm:physical-budget-boundary`        Full         `L.Physical.feasible_iff_floor_le_budget`, `L.Physical.higher_leverage_same_caps_preserves_feasibility_under_same_budget`, `L.Physical.infeasible_of_budget_lt_floor`

  `thm:physical-energy-floor`           Full         `L.Physical.energyLowerBound_eq_joules_times_dof`, `L.Physical.lower_dof_lower_energy`, `L.Physical.positive_energy_of_wellformed_arch`

  `thm:ssot-leverage`                   Full         `L.SSOT.modification_ratio`, `L.SSOT.paper2_leverage_ratio`, `L.SSOT.ssot_leverage_dominance`

  `thm:testable-prediction`             Full         `L.testable_modification_prediction`
  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

*Notes:* *(1) Full rows come from theorem-local inline anchors in this paper.* *(2) Derived rows are filled by dependency/scaffold claim-handle derivation (same paper-handle label across proof dependencies).* *(3) Unmapped means no local anchor and no derivable dependency support were found.*

*Auto summary: mapped 27/28 (full=27, derived=0, unmapped=1).*


+----------------------------------------------------------------------------------------------------------------------------------+
| Lean handle entry                                                                                                                |
+:=================================================================================================================================+
| Lean handle entry (continued)                                                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| ::: {#lh:AC1}                                                                                                                    |
| `AC1`                                                                                                                            |
| :::                                                                                                                              |
|                                                                                                                                  |
| `DecisionQuotient.ClaimClosure.AtomicCircuitExports.AC1`                                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AC3`]{#lh:AC3}`DecisionQuotient.ClaimClosure.AtomicCircuitExports.AC3`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AC4`]{#lh:AC4}`DecisionQuotient.ClaimClosure.AtomicCircuitExports.AC4`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AC5`]{#lh:AC5}`DecisionQuotient.ClaimClosure.AtomicCircuitExports.AC5`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AC6`]{#lh:AC6}`DecisionQuotient.ClaimClosure.AtomicCircuitExports.AC6`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AC8`]{#lh:AC8}`DecisionQuotient.ClaimClosure.AtomicCircuitExports.AC8`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AC9`]{#lh:AC9}`DecisionQuotient.ClaimClosure.AtomicCircuitExports.AC9`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AC11`]{#lh:AC11}`DecisionQuotient.ClaimClosure.AtomicCircuitExports.AC11`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AN1`]{#lh:AN1}`DecisionQuotient.Physics.AssumptionNecessity.no_assumption_free_proof_of_refutable_claim`                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AN2`]{#lh:AN2}`DecisionQuotient.Physics.AssumptionNecessity.countermodel_violates_some_assumption`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AN3`]{#lh:AN3}`DecisionQuotient.Physics.AssumptionNecessity.physical_claim_requires_physical_assumption`                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AN4`]{#lh:AN4}`DecisionQuotient.Physics.AssumptionNecessity.physical_claim_requires_empirically_justified_physical_assumption` |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AN5`]{#lh:AN5}`DecisionQuotient.Physics.AssumptionNecessity.strong_physical_no_go_meta`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AQ1`]{#lh:AQ1}`DecisionQuotient.ClaimClosure.AQ1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AQ2`]{#lh:AQ2}`DecisionQuotient.ClaimClosure.AQ2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AQ3`]{#lh:AQ3}`DecisionQuotient.ClaimClosure.AQ3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AQ4`]{#lh:AQ4}`DecisionQuotient.ClaimClosure.AQ4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AQ5`]{#lh:AQ5}`DecisionQuotient.ClaimClosure.AQ5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AQ6`]{#lh:AQ6}`DecisionQuotient.ClaimClosure.AQ6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AQ7`]{#lh:AQ7}`DecisionQuotient.ClaimClosure.AQ7`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AQ8`]{#lh:AQ8}`DecisionQuotient.ClaimClosure.AQ8`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG1`]{#lh:ARG1}`PhysicalComplexity.AccessRegime.PhysicalDevice`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG2`]{#lh:ARG2}`PhysicalComplexity.AccessRegime.AccessRegime`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG3`]{#lh:ARG3}`PhysicalComplexity.AccessRegime.RegimeEval`                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG4`]{#lh:ARG4}`PhysicalComplexity.AccessRegime.RegimeSample`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG5`]{#lh:ARG5}`PhysicalComplexity.AccessRegime.RegimeProof`                                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG6`]{#lh:ARG6}`PhysicalComplexity.AccessRegime.RegimeWithCertificate`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG7`]{#lh:ARG7}`PhysicalComplexity.AccessRegime.RegimeEvalOn`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG8`]{#lh:ARG8}`PhysicalComplexity.AccessRegime.RegimeSampleOn`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG9`]{#lh:ARG9}`PhysicalComplexity.AccessRegime.RegimeProofOn`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG10`]{#lh:ARG10}`PhysicalComplexity.AccessRegime.RegimeWithCertificateOn`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG11`]{#lh:ARG11}`PhysicalComplexity.AccessRegime.HardUnderEval`                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG12`]{#lh:ARG12}`PhysicalComplexity.AccessRegime.AuditableWithCertificate`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG13`]{#lh:ARG13}`PhysicalComplexity.AccessRegime.certificate_upgrades_regime`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG14`]{#lh:ARG14}`PhysicalComplexity.AccessRegime.certificate_upgrades_regime_on`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG15`]{#lh:ARG15}`PhysicalComplexity.AccessRegime.physical_succinct_certification_hard`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG16`]{#lh:ARG16}`PhysicalComplexity.AccessRegime.certificate_amortizes_hardness`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG17`]{#lh:ARG17}`PhysicalComplexity.AccessRegime.regime_upgrade_with_certificate`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG18`]{#lh:ARG18}`PhysicalComplexity.AccessRegime.regime_upgrade_with_certificate_on`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG19`]{#lh:ARG19}`PhysicalComplexity.AccessRegime.AccessChannelLaw`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ARG20`]{#lh:ARG20}`PhysicalComplexity.AccessRegime.FiveWayMeet`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AXM1`]{#lh:AXM1}`complete_mono`                                                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AXM2`]{#lh:AXM2}`completeD_mono`                                                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AXM3`]{#lh:AXM3}`minimal_no_redundant_axes`                                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`AXM4`]{#lh:AXM4}`semantically_minimal_implies_independent`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA1`]{#lh:BA1}`DecisionQuotient.Physics.BoundedAcquisition.BoundedRegion`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA2`]{#lh:BA2}`DecisionQuotient.Physics.BoundedAcquisition.acquisition_rate_bound`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA3`]{#lh:BA3}`DecisionQuotient.Physics.BoundedAcquisition.acquisitions_are_transitions`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA4`]{#lh:BA4}`DecisionQuotient.Physics.BoundedAcquisition.one_bit_per_transition`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA5`]{#lh:BA5}`DecisionQuotient.Physics.BoundedAcquisition.resolution_reads_sufficient`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA6`]{#lh:BA6}`DecisionQuotient.Physics.BoundedAcquisition.srank_le_resolution_bits`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA7`]{#lh:BA7}`DecisionQuotient.Physics.BoundedAcquisition.energy_ge_srank_cost`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA8`]{#lh:BA8}`DecisionQuotient.Physics.BoundedAcquisition.srank_one_energy_minimum`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA9`]{#lh:BA9}`DecisionQuotient.Physics.BoundedAcquisition.physical_grounding_bundle`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BA10`]{#lh:BA10}`DecisionQuotient.Physics.BoundedAcquisition.counting_gap_theorem`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BAS1`]{#lh:BAS1}`correctness_forcing`                                                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BAS2`]{#lh:BAS2}`dof_inconsistency_potential`                                                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BAS3`]{#lh:BAS3}`dof_gt_one_inconsistent`                                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BB1`]{#lh:BB1}`DecisionQuotient.BayesianDQ`                                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BB2`]{#lh:BB2}`DecisionQuotient.BayesianDQ.certaintyGain`                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BB3`]{#lh:BB3}`DecisionQuotient.dq_is_bayesian_certainty_fraction`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BB4`]{#lh:BB4}`DecisionQuotient.bayesian_dq_matches_physics_dq`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BB5`]{#lh:BB5}`DecisionQuotient.dq_derived_from_bayes`                                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BC1`]{#lh:BC1}`DecisionQuotient.Foundations.counting_nonneg`                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BC2`]{#lh:BC2}`DecisionQuotient.Foundations.counting_total`                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BC3`]{#lh:BC3}`DecisionQuotient.Foundations.counting_additive`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BC4`]{#lh:BC4}`DecisionQuotient.Foundations.bayes_from_conditional`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BC5`]{#lh:BC5}`DecisionQuotient.Foundations.entropy_contraction`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BF1`]{#lh:BF1}`DecisionQuotient.certainty_of_not_nondegenerateBelief`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BF2`]{#lh:BF2}`DecisionQuotient.nondegenerateBelief_of_uncertaintyForced`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BF3`]{#lh:BF3}`DecisionQuotient.forced_action_under_uncertainty`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BF4`]{#lh:BF4}`DecisionQuotient.bayes_update_exists_of_nondegenerateBelief`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BND1`]{#lh:BND1}`ssot_upper_bound`                                                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BND2`]{#lh:BND2}`non_ssot_lower_bound`                                                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BND3`]{#lh:BND3}`ssot_advantage_unbounded`                                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`BND4`]{#lh:BND4}`ClaimClosure.arbitrary_reduction_factor`                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CAP1`]{#lh:CAP1}`ClaimClosure.cap_encoding_conditional`                                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CAP2`]{#lh:CAP2}`ssot_guarantees_coherence`                                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CAP3`]{#lh:CAP3}`non_ssot_permits_incoherence`                                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC1`]{#lh:CC1}`DecisionQuotient.ClaimClosure.RegimeSimulation`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC2`]{#lh:CC2}`DecisionQuotient.ClaimClosure.adq_ordering`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC3`]{#lh:CC3}`DecisionQuotient.ClaimClosure.system_transfer_licensed_iff_snapshot`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC4`]{#lh:CC4}`DecisionQuotient.ClaimClosure.anchor_sigma2p_complete_conditional`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC5`]{#lh:CC5}`DecisionQuotient.ClaimClosure.anchor_sigma2p_reduction_core`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC6`]{#lh:CC6}`DecisionQuotient.ClaimClosure.anchor_query_relation_false_iff`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC7`]{#lh:CC7}`DecisionQuotient.ClaimClosure.anchor_query_relation_true_iff`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC8`]{#lh:CC8}`DecisionQuotient.ClaimClosure.boundaryCharacterized_iff_exists_sufficient_subset`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC9`]{#lh:CC9}`DecisionQuotient.ClaimClosure.bounded_actions_detectable`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC10`]{#lh:CC10}`DecisionQuotient.ClaimClosure.bridge_boundary_represented_family`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC11`]{#lh:CC11}`DecisionQuotient.ClaimClosure.bridge_failure_witness_non_one_step`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC12`]{#lh:CC12}`DecisionQuotient.ClaimClosure.bridge_transfer_iff_one_step_class`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC13`]{#lh:CC13}`DecisionQuotient.ClaimClosure.certified_total_bits_split_core`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC14`]{#lh:CC14}`DecisionQuotient.ClaimClosure.cost_asymmetry_eth_conditional`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC15`]{#lh:CC15}`DecisionQuotient.ClaimClosure.declaredBudgetSlice`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC16`]{#lh:CC16}`DecisionQuotient.ClaimClosure.declaredRegimeFamily_complete`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC17`]{#lh:CC17}`DecisionQuotient.ClaimClosure.declared_physics_no_universal_exact_certifier_core`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC18`]{#lh:CC18}`DecisionQuotient.ClaimClosure.dichotomy_conditional`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC19`]{#lh:CC19}`DecisionQuotient.ClaimClosure.epsilon_admissible_iff_raw_lt_certified_total_core`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC20`]{#lh:CC20}`DecisionQuotient.ClaimClosure.exact_admissible_iff_raw_lt_certified_total_core`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC21`]{#lh:CC21}`DecisionQuotient.ClaimClosure.exact_certainty_inflation_under_hardness_core`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC22`]{#lh:CC22}`DecisionQuotient.ClaimClosure.exact_raw_eq_certified_iff_certainty_inflation_core`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC23`]{#lh:CC23}`DecisionQuotient.ClaimClosure.exact_raw_only_of_no_exact_admissible_core`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC24`]{#lh:CC24}`DecisionQuotient.ClaimClosure.explicit_assumptions_required_of_not_excused_core`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC25`]{#lh:CC25}`DecisionQuotient.ClaimClosure.explicit_state_upper_core`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC26`]{#lh:CC26}`DecisionQuotient.ClaimClosure.hard_family_all_coords_core`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC27`]{#lh:CC27}`DecisionQuotient.ClaimClosure.horizonTwoWitness_immediate_empty_sufficient`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC28`]{#lh:CC28}`DecisionQuotient.ClaimClosure.horizon_gt_one_bridge_can_fail_on_sufficiency`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC29`]{#lh:CC29}`DecisionQuotient.ClaimClosure.information_barrier_opt_oracle_core`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC30`]{#lh:CC30}`DecisionQuotient.ClaimClosure.information_barrier_state_batch_core`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC31`]{#lh:CC31}`DecisionQuotient.ClaimClosure.information_barrier_value_entry_core`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC32`]{#lh:CC32}`DecisionQuotient.ClaimClosure.integrity_resource_bound_for_sufficiency`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC33`]{#lh:CC33}`DecisionQuotient.ClaimClosure.integrity_universal_applicability_core`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC34`]{#lh:CC34}`DecisionQuotient.ClaimClosure.meta_coordinate_irrelevant_of_invariance_on_declared_slice`                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC35`]{#lh:CC35}`DecisionQuotient.ClaimClosure.meta_coordinate_not_relevant_on_declared_slice`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC36`]{#lh:CC36}`DecisionQuotient.ClaimClosure.minsuff_collapse_core`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC37`]{#lh:CC37}`DecisionQuotient.ClaimClosure.minsuff_collapse_to_conp_conditional`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC38`]{#lh:CC38}`DecisionQuotient.ClaimClosure.minsuff_conp_complete_conditional`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC39`]{#lh:CC39}`DecisionQuotient.ClaimClosure.no_auto_minimize_of_p_neq_conp`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC40`]{#lh:CC40}`DecisionQuotient.ClaimClosure.no_exact_claim_admissible_under_hardness_core`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC41`]{#lh:CC41}`DecisionQuotient.ClaimClosure.no_exact_claim_under_declared_assumptions_unless_excused_core`                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC42`]{#lh:CC42}`DecisionQuotient.ClaimClosure.no_exact_identifier_implies_not_boundary_characterized`                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC43`]{#lh:CC43}`DecisionQuotient.ClaimClosure.no_uncertified_exact_claim_core`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC44`]{#lh:CC44}`DecisionQuotient.ClaimClosure.one_step_bridge`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC45`]{#lh:CC45}`DecisionQuotient.ClaimClosure.oracle_lattice_transfer_as_regime_simulation`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC46`]{#lh:CC46}`DecisionQuotient.ClaimClosure.physical_crossover_above_cap_core`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC47`]{#lh:CC47}`DecisionQuotient.ClaimClosure.physical_crossover_core`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC48`]{#lh:CC48}`DecisionQuotient.ClaimClosure.physical_crossover_hardness_core`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC49`]{#lh:CC49}`DecisionQuotient.ClaimClosure.physical_crossover_policy_core`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC50`]{#lh:CC50}`DecisionQuotient.ClaimClosure.process_bridge_failure_witness`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC51`]{#lh:CC51}`DecisionQuotient.ClaimClosure.poseAnchorQuery`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC52`]{#lh:CC52}`DecisionQuotient.ClaimClosure.pose_returns_anchor_query_object`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC53`]{#lh:CC53}`DecisionQuotient.ClaimClosure.posed_anchor_checked_true_implies_truth`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC54`]{#lh:CC54}`DecisionQuotient.ClaimClosure.posed_anchor_exact_claim_admissible_iff_competent`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC55`]{#lh:CC55}`DecisionQuotient.ClaimClosure.posed_anchor_exact_claim_requires_evidence`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC56`]{#lh:CC56}`DecisionQuotient.ClaimClosure.posed_anchor_no_competence_no_exact_claim`                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC57`]{#lh:CC57}`DecisionQuotient.ClaimClosure.posed_anchor_query_truth_iff_exists_anchor`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC58`]{#lh:CC58}`DecisionQuotient.ClaimClosure.posed_anchor_query_truth_iff_exists_forall`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC59`]{#lh:CC59}`DecisionQuotient.ClaimClosure.posed_anchor_signal_positive_certified_implies_admissible`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC60`]{#lh:CC60}`DecisionQuotient.ClaimClosure.query_obstruction_boolean_corollary`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC61`]{#lh:CC61}`DecisionQuotient.ClaimClosure.query_obstruction_finite_state_core`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC62`]{#lh:CC62}`DecisionQuotient.ClaimClosure.regime_core_claim_proved`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC63`]{#lh:CC63}`DecisionQuotient.ClaimClosure.regime_simulation_transfers_hardness`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC64`]{#lh:CC64}`DecisionQuotient.ClaimClosure.reusable_heuristic_of_detectable`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC65`]{#lh:CC65}`DecisionQuotient.ClaimClosure.selectorSufficient_not_implies_setSufficient`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC66`]{#lh:CC66}`DecisionQuotient.ClaimClosure.separable_detectable`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC67`]{#lh:CC67}`DecisionQuotient.ClaimClosure.snapshot_vs_process_typed_boundary`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC68`]{#lh:CC68}`DecisionQuotient.ClaimClosure.standard_assumption_ledger_unpack`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC69`]{#lh:CC69}`DecisionQuotient.ClaimClosure.stochastic_objective_bridge_can_fail_on_sufficiency`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC70`]{#lh:CC70}`DecisionQuotient.ClaimClosure.subproblem_hardness_lifts_to_full`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC71`]{#lh:CC71}`DecisionQuotient.ClaimClosure.subproblem_transfer_as_regime_simulation`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC72`]{#lh:CC72}`DecisionQuotient.ClaimClosure.sufficiency_conp_complete_conditional`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC73`]{#lh:CC73}`DecisionQuotient.ClaimClosure.sufficiency_conp_reduction_core`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC74`]{#lh:CC74}`DecisionQuotient.ClaimClosure.sufficiency_iff_dq_ratio`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC75`]{#lh:CC75}`DecisionQuotient.ClaimClosure.sufficiency_iff_projectedOptCover_eq_opt`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC76`]{#lh:CC76}`DecisionQuotient.ClaimClosure.thermo_conservation_additive_core`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC77`]{#lh:CC77}`DecisionQuotient.ClaimClosure.thermo_energy_carbon_lift_core`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC78`]{#lh:CC78}`DecisionQuotient.ClaimClosure.thermo_eventual_lift_core`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC79`]{#lh:CC79}`DecisionQuotient.ClaimClosure.thermo_hardness_bundle_core`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC80`]{#lh:CC80}`DecisionQuotient.ClaimClosure.thermo_mandatory_cost_core`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC81`]{#lh:CC81}`DecisionQuotient.ClaimClosure.tractable_bounded_core`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC82`]{#lh:CC82}`DecisionQuotient.ClaimClosure.tractable_separable_core`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC83`]{#lh:CC83}`DecisionQuotient.ClaimClosure.tractable_subcases_conditional`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC84`]{#lh:CC84}`DecisionQuotient.ClaimClosure.tractable_tree_core`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC85`]{#lh:CC85}`DecisionQuotient.ClaimClosure.transition_coupled_bridge_can_fail_on_sufficiency`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC86`]{#lh:CC86}`DecisionQuotient.ClaimClosure.tree_structure_detectable`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC87`]{#lh:CC87}`DecisionQuotient.ClaimClosure.typed_claim_admissibility_core`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC88`]{#lh:CC88}`DecisionQuotient.ClaimClosure.typed_static_class_completeness`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CC89`]{#lh:CC89}`DecisionQuotient.ClaimClosure.universal_solver_framing_core`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CCC1`]{#lh:CCC1}`DecisionQuotient.CC.anchor_sigma2p_complete_conditional`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CCC2`]{#lh:CCC2}`DecisionQuotient.CC.cost_asymmetry_eth_conditional`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CCC3`]{#lh:CCC3}`DecisionQuotient.CC.dichotomy_conditional`                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CCC4`]{#lh:CCC4}`DecisionQuotient.CC.minsuff_collapse_to_conp_conditional`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CCC5`]{#lh:CCC5}`DecisionQuotient.CC.minsuff_conp_complete_conditional`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CCC6`]{#lh:CCC6}`DecisionQuotient.CC.sufficiency_conp_complete_conditional`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CCC7`]{#lh:CCC7}`DecisionQuotient.CC.tractable_subcases_conditional`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF1`]{#lh:CF1}`DecisionQuotient.Physics.ConstraintForcing.laws_not_determined_of_parameter_separation`                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF2`]{#lh:CF2}`DecisionQuotient.Physics.ConstraintForcing.logic_time_not_sufficient_for_unique_law`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF3`]{#lh:CF3}`DecisionQuotient.Physics.ConstraintForcing.laws_determined_implies_objective_determined`                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF4`]{#lh:CF4}`DecisionQuotient.Physics.ConstraintForcing.objective_not_determined_of_parameter_separation`                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF5`]{#lh:CF5}`DecisionQuotient.Physics.ConstraintForcing.forcedDecisionBits_pos_of_deadline`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF6`]{#lh:CF6}`DecisionQuotient.Physics.ConstraintForcing.actionForced_of_deadline`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF7`]{#lh:CF7}`DecisionQuotient.Physics.ConstraintForcing.nondegenerateBelief_of_deadline_and_uncertainty`                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF8`]{#lh:CF8}`DecisionQuotient.Physics.ConstraintForcing.forced_decision_implies_positive_landauer_cost`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CF9`]{#lh:CF9}`DecisionQuotient.Physics.ConstraintForcing.forced_decision_implies_positive_nv_work`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CH1`]{#lh:CH1}`DecisionQuotient.ClaimClosure.CH1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CH2`]{#lh:CH2}`DecisionQuotient.ClaimClosure.CH2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CH3`]{#lh:CH3}`DecisionQuotient.ClaimClosure.CH3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CH5`]{#lh:CH5}`DecisionQuotient.ClaimClosure.CH5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CH6`]{#lh:CH6}`DecisionQuotient.ClaimClosure.CH6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CIA1`]{#lh:CIA1}`ClaimClosure.ClassicalInfoAssumptions`                                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`COH1`]{#lh:COH1}`dof_one_implies_coherent`                                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`COH2`]{#lh:COH2}`dof_gt_one_incoherence_possible`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`COH3`]{#lh:COH3}`determinate_truth_forces_ssot`                                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CPL1`]{#lh:CPL1}`cost_ratio_eq_dof`                                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CR1`]{#lh:CR1}`DecisionQuotient.ConfigReduction.config_sufficiency_iff_behavior_preserving`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT1`]{#lh:CT1}`DecisionQuotient.Physics.ClaimTransport.PhysicalEncoding`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT2`]{#lh:CT2}`DecisionQuotient.Physics.ClaimTransport.physical_claim_lifts_from_core`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT3`]{#lh:CT3}`DecisionQuotient.Physics.ClaimTransport.physical_claim_lifts_from_core_conditional`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT4`]{#lh:CT4}`DecisionQuotient.Physics.ClaimTransport.physical_counterexample_yields_core_counterexample`                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT5`]{#lh:CT5}`DecisionQuotient.Physics.ClaimTransport.physical_counterexample_invalidates_core_rule`                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT6`]{#lh:CT6}`DecisionQuotient.Physics.ClaimTransport.no_physical_counterexample_of_core_theorem`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT7`]{#lh:CT7}`DecisionQuotient.Physics.ClaimTransport.LawGapInstance`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT8`]{#lh:CT8}`DecisionQuotient.Physics.ClaimTransport.lawGapEncoding`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT9`]{#lh:CT9}`DecisionQuotient.Physics.ClaimTransport.lawGapPhysicalClaim`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT10`]{#lh:CT10}`DecisionQuotient.Physics.ClaimTransport.law_gap_physical_claim_holds`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT11`]{#lh:CT11}`DecisionQuotient.Physics.ClaimTransport.no_law_gap_counterexample`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CT12`]{#lh:CT12}`DecisionQuotient.Physics.ClaimTransport.physical_bridge_bundle`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV1`]{#lh:CV1}`DecisionQuotient.Physics.Conversation.RecurrentCircuit`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV2`]{#lh:CV2}`DecisionQuotient.Physics.Conversation.CoupledConversation`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV3`]{#lh:CV3}`DecisionQuotient.Physics.Conversation.JointState`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV4`]{#lh:CV4}`DecisionQuotient.Physics.Conversation.tick_uses_shared_node`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV5`]{#lh:CV5}`DecisionQuotient.Physics.Conversation.tick_shared_is_merged_emissions`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV6`]{#lh:CV6}`DecisionQuotient.Physics.Conversation.channel_projection_eq_iff_quantized_eq`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV7`]{#lh:CV7}`DecisionQuotient.Physics.Conversation.clamp_projection_eq_iff_same_clamped_bit`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV10`]{#lh:CV10}`DecisionQuotient.Physics.Conversation.explanationGap_add_explanationBits`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV11`]{#lh:CV11}`DecisionQuotient.Physics.Conversation.toClaimReport`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV12`]{#lh:CV12}`DecisionQuotient.Physics.Conversation.abstain_iff_no_answer`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV13`]{#lh:CV13}`DecisionQuotient.Physics.Conversation.yes_no_iff_exact_claim`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV14`]{#lh:CV14}`DecisionQuotient.Physics.Conversation.toReportSignal_completion_defined_of_budget`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV15`]{#lh:CV15}`DecisionQuotient.Physics.Conversation.toReportSignal_signal_consistent_zero_certified`                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV16`]{#lh:CV16}`DecisionQuotient.Physics.Conversation.abstain_report_can_carry_explanation`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV17`]{#lh:CV17}`DecisionQuotient.Physics.Conversation.clampDecisionEvent_iff_bitOps_pos`                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV18`]{#lh:CV18}`DecisionQuotient.Physics.Conversation.clamp_event_implies_positive_energy`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV19`]{#lh:CV19}`DecisionQuotient.Physics.Conversation.BinaryAnswer`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV20`]{#lh:CV20}`DecisionQuotient.Physics.Conversation.ConversationReport`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV21`]{#lh:CV21}`DecisionQuotient.Physics.Conversation.explanationGap`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV26`]{#lh:CV26}`DecisionQuotient.Physics.Conversation.toClaimReport_ne_epsilon`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV27`]{#lh:CV27}`DecisionQuotient.Physics.Conversation.toReportSignal`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`CV28`]{#lh:CV28}`DecisionQuotient.Physics.Conversation.toReportSignal_declares_bound`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC1`]{#lh:DC1}`DecisionQuotient.StochasticSequential.static_stochastic_strict_separation`                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC2`]{#lh:DC2}`DecisionQuotient.StochasticSequential.stochastic_sequential_strict_separation`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC3`]{#lh:DC3}`DecisionQuotient.StochasticSequential.complexity_dichotomy_hierarchy`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC4`]{#lh:DC4}`DecisionQuotient.StochasticSequential.regime_hierarchy`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC5`]{#lh:DC5}`DecisionQuotient.StochasticSequential.coNP_subset_PP`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC6`]{#lh:DC6}`DecisionQuotient.StochasticSequential.PP_subset_PSPACE`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC7`]{#lh:DC7}`DecisionQuotient.StochasticSequential.coNP_subset_PSPACE`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC8`]{#lh:DC8}`DecisionQuotient.StochasticSequential.static_to_coNP`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC9`]{#lh:DC9}`DecisionQuotient.StochasticSequential.stochastic_to_PP`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC10`]{#lh:DC10}`DecisionQuotient.StochasticSequential.sequential_to_PSPACE`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC11`]{#lh:DC11}`DecisionQuotient.StochasticSequential.ClaimClosure.claim_six_subcases`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC12`]{#lh:DC12}`DecisionQuotient.StochasticSequential.ClaimClosure.claim_hierarchy`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC13`]{#lh:DC13}`DecisionQuotient.StochasticSequential.ClaimClosure.claim_tractable_subcases_to_P`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC14`]{#lh:DC14}`DecisionQuotient.StochasticSequential.stochastic_dichotomy`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC15`]{#lh:DC15}`DecisionQuotient.StochasticSequential.above_threshold_hard`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC16`]{#lh:DC16}`DecisionQuotient.StochasticSequential.StochasticAnchorSufficient`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC17`]{#lh:DC17}`DecisionQuotient.StochasticSequential.StochasticAnchorSufficiencyCheck`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC18`]{#lh:DC18}`DecisionQuotient.StochasticSequential.stochastic_anchor_check_iff`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC19`]{#lh:DC19}`DecisionQuotient.StochasticSequential.stochastic_anchor_sufficient_of_stochastic_sufficient`                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC20`]{#lh:DC20}`DecisionQuotient.StochasticSequential.SequentialAnchorSufficient`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC21`]{#lh:DC21}`DecisionQuotient.StochasticSequential.SequentialAnchorSufficiencyCheck`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC22`]{#lh:DC22}`DecisionQuotient.StochasticSequential.sequential_anchor_check_iff`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC23`]{#lh:DC23}`DecisionQuotient.StochasticSequential.sequential_anchor_sufficient_of_sequential_sufficient`                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC24`]{#lh:DC24}`DecisionQuotient.StochasticSequential.StochasticAnchorCheckInstance`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC25`]{#lh:DC25}`DecisionQuotient.StochasticSequential.reduceMAJSAT_correct_anchor_strict`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC26`]{#lh:DC26}`DecisionQuotient.StochasticSequential.reduceMAJSAT_to_stochastic_anchor_reduction`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC27`]{#lh:DC27}`DecisionQuotient.StochasticSequential.SequentialAnchorCheckInstance`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC28`]{#lh:DC28}`DecisionQuotient.StochasticSequential.reduceTQBF_correct_anchor`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC29`]{#lh:DC29}`DecisionQuotient.StochasticSequential.reduceTQBF_to_sequential_anchor_reduction`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC30`]{#lh:DC30}`DecisionQuotient.StochasticSequential.StatePotential`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC31`]{#lh:DC31}`DecisionQuotient.StochasticSequential.utilityFromPotentialDrop_le_iff_nextPotential_ge`                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC32`]{#lh:DC32}`DecisionQuotient.StochasticSequential.utility_from_action_state_potential`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC33`]{#lh:DC33}`DecisionQuotient.StochasticSequential.stochasticExpectedUtility_eq_neg_expectedActionPotential`               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC34`]{#lh:DC34}`DecisionQuotient.StochasticSequential.stochasticExpectedUtility_le_iff_expectedActionPotential_ge`            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC35`]{#lh:DC35}`DecisionQuotient.StochasticSequential.landauerEnergyFloor_nonneg`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC36`]{#lh:DC36}`DecisionQuotient.StochasticSequential.landauerEnergyFloor_mono_bits`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DC37`]{#lh:DC37}`DecisionQuotient.StochasticSequential.thermodynamicCost_eq_landauerEnergyFloorRoom_states`                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DE1`]{#lh:DE1}`DecisionQuotient.ClaimClosure.DE1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DE2`]{#lh:DE2}`DecisionQuotient.ClaimClosure.DE2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DE3`]{#lh:DE3}`DecisionQuotient.ClaimClosure.DE3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DE4`]{#lh:DE4}`DecisionQuotient.ClaimClosure.DE4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DER1`]{#lh:DER1}`all_derived_from_source`                                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DER2`]{#lh:DER2}`ClaimClosure.derivation_preserves_coherence_core`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DES1`]{#lh:DES1}`ClaimClosure.design_necessity`                                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG1`]{#lh:DG1}`DecisionQuotient.Outside`                                                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG2`]{#lh:DG2}`DecisionQuotient.anchoredSlice`                                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG3`]{#lh:DG3}`DecisionQuotient.anchoredSliceEquivOutside`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG4`]{#lh:DG4}`DecisionQuotient.card_outside_eq_sub`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG5`]{#lh:DG5}`DecisionQuotient.card_anchoredSlice`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG6`]{#lh:DG6}`DecisionQuotient.card_anchoredSlice_eq_pow_sub`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG7`]{#lh:DG7}`DecisionQuotient.card_anchoredSlice_eq_uniform`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG8`]{#lh:DG8}`DecisionQuotient.anchoredSlice_mul_fixed_eq_full`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG9`]{#lh:DG9}`DecisionQuotient.constantBoolDP`                                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG10`]{#lh:DG10}`DecisionQuotient.firstCoordDP`                                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG11`]{#lh:DG11}`DecisionQuotient.constantBoolDP_opt`                                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG12`]{#lh:DG12}`DecisionQuotient.firstCoordDP_opt`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG13`]{#lh:DG13}`DecisionQuotient.constantBoolDP_empty_sufficient`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG14`]{#lh:DG14}`DecisionQuotient.firstCoordDP_empty_not_sufficient`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG15`]{#lh:DG15}`DecisionQuotient.boolHypercube_node_count`                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG16`]{#lh:DG16}`DecisionQuotient.node_count_does_not_determine_edge_geometry`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG17`]{#lh:DG17}`DecisionQuotient.DecisionProblem.edgeOnComplement`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DG18`]{#lh:DG18}`DecisionQuotient.DecisionProblem.edgeOnComplement_iff_not_sufficient`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DP1`]{#lh:DP1}`DecisionQuotient.DecisionProblem.minimalSufficient_iff_relevant`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DP2`]{#lh:DP2}`DecisionQuotient.DecisionProblem.relevantSet_is_minimal`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DP3`]{#lh:DP3}`DecisionQuotient.DecisionProblem.sufficient_implies_selectorSufficient`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DP4`]{#lh:DP4}`DecisionQuotient.ClaimClosure.DecisionProblem.epsOpt_zero_eq_opt`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DP5`]{#lh:DP5}`DecisionQuotient.ClaimClosure.DecisionProblem.sufficient_iff_zeroEpsilonSufficient`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DP6`]{#lh:DP6}`DecisionQuotient.ClaimClosure.DP6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DP7`]{#lh:DP7}`DecisionQuotient.ClaimClosure.DP7`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DP8`]{#lh:DP8}`DecisionQuotient.ClaimClosure.DP8`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DQ1`]{#lh:DQ1}`DecisionQuotient.ClaimClosure.DQ1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DQ2`]{#lh:DQ2}`DecisionQuotient.ClaimClosure.DQ2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DQ3`]{#lh:DQ3}`DecisionQuotient.ClaimClosure.DQ3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DQ4`]{#lh:DQ4}`DecisionQuotient.ClaimClosure.DQ4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DQ5`]{#lh:DQ5}`DecisionQuotient.ClaimClosure.DQ5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DQ6`]{#lh:DQ6}`DecisionQuotient.ClaimClosure.DQ6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DQ7`]{#lh:DQ7}`DecisionQuotient.ClaimClosure.DQ7`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DQ8`]{#lh:DQ8}`DecisionQuotient.ClaimClosure.DQ8`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DS1`]{#lh:DS1}`DecisionQuotient.ClaimClosure.DS1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DS2`]{#lh:DS2}`DecisionQuotient.ClaimClosure.DS2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DS3`]{#lh:DS3}`DecisionQuotient.ClaimClosure.DS3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DS4`]{#lh:DS4}`DecisionQuotient.ClaimClosure.DS4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DS5`]{#lh:DS5}`DecisionQuotient.ClaimClosure.DS5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DS6`]{#lh:DS6}`DecisionQuotient.ClaimClosure.DS6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT1`]{#lh:DT1}`DecisionQuotient.Physics.DecisionTime.TimedState`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT2`]{#lh:DT2}`DecisionQuotient.Physics.DecisionTime.DecisionProcess`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT3`]{#lh:DT3}`DecisionQuotient.Physics.DecisionTime.tick`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT4`]{#lh:DT4}`DecisionQuotient.Physics.DecisionTime.DecisionEvent`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT5`]{#lh:DT5}`DecisionQuotient.Physics.DecisionTime.TimeUnitStep`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT6`]{#lh:DT6}`DecisionQuotient.Physics.DecisionTime.time_is_discrete`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT7`]{#lh:DT7}`DecisionQuotient.Physics.DecisionTime.time_coordinate_falsifiable`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT8`]{#lh:DT8}`DecisionQuotient.Physics.DecisionTime.tick_increments_time`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT9`]{#lh:DT9}`DecisionQuotient.Physics.DecisionTime.tick_decision_witness`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT10`]{#lh:DT10}`DecisionQuotient.Physics.DecisionTime.tick_is_decision_event`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT11`]{#lh:DT11}`DecisionQuotient.Physics.DecisionTime.decision_event_implies_time_unit`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT12`]{#lh:DT12}`DecisionQuotient.Physics.DecisionTime.decision_taking_place_is_unit_of_time`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT13`]{#lh:DT13}`DecisionQuotient.Physics.DecisionTime.decision_event_iff_eq_tick`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT14`]{#lh:DT14}`DecisionQuotient.Physics.DecisionTime.run`                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT15`]{#lh:DT15}`DecisionQuotient.Physics.DecisionTime.run_time_exact`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT16`]{#lh:DT16}`DecisionQuotient.Physics.DecisionTime.run_elapsed_time_eq_ticks`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT17`]{#lh:DT17}`DecisionQuotient.Physics.DecisionTime.decisionTrace`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT18`]{#lh:DT18}`DecisionQuotient.Physics.DecisionTime.decisionTrace_length_eq_ticks`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT19`]{#lh:DT19}`DecisionQuotient.Physics.DecisionTime.decision_count_equals_elapsed_time`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT20`]{#lh:DT20}`DecisionQuotient.Physics.DecisionTime.SubstrateKind`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT21`]{#lh:DT21}`DecisionQuotient.Physics.DecisionTime.SubstrateModel`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT22`]{#lh:DT22}`DecisionQuotient.Physics.DecisionTime.substrate_step_realizes_decision_event`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT23`]{#lh:DT23}`DecisionQuotient.Physics.DecisionTime.substrate_step_is_time_unit`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`DT24`]{#lh:DT24}`DecisionQuotient.Physics.DecisionTime.time_unit_law_substrate_invariant`                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`EI1`]{#lh:EI1}`DecisionQuotient.ThermodynamicLift.energy_ge_kbt_nat_entropy`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`EI2`]{#lh:EI2}`DecisionQuotient.ThermodynamicLift.energy_ground_state_tracks_entropy`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`EI4`]{#lh:EI4}`DecisionQuotient.ThermodynamicLift.landauerJoulesPerBit_pos`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`EI5`]{#lh:EI5}`DecisionQuotient.ThermodynamicLift.neukart_vinokur_duality`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ENT1`]{#lh:ENT1}`Entropy.ClassicalEntropyAssumptions`                                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`EP1`]{#lh:EP1}`DecisionQuotient.Physics.LocalityPhysics.landauer_principle`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`EP2`]{#lh:EP2}`DecisionQuotient.Physics.LocalityPhysics.finite_regional_energy`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`EP3`]{#lh:EP3}`DecisionQuotient.Physics.LocalityPhysics.finite_signal_speed`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`EP4`]{#lh:EP4}`DecisionQuotient.Physics.LocalityPhysics.nontrivial_physics`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FI3`]{#lh:FI3}`DecisionQuotient.FunctionalInformation.functional_information_from_counting`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FI6`]{#lh:FI6}`DecisionQuotient.FunctionalInformation.functional_information_from_thermodynamics`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FI7`]{#lh:FI7}`DecisionQuotient.FunctionalInformation.first_principles_thermo_coincide`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FLP1`]{#lh:FLP1}`ClaimClosure.static_flp_core`                                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FN7`]{#lh:FN7}`DecisionQuotient.BayesOptimalityProof.KL_nonneg`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FN8`]{#lh:FN8}`DecisionQuotient.BayesOptimalityProof.entropy_le_crossEntropy`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FN12`]{#lh:FN12}`DecisionQuotient.BayesOptimalityProof.crossEntropy_eq_entropy_add_KL`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FN14`]{#lh:FN14}`DecisionQuotient.BayesOptimalityProof.bayes_is_optimal`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FN15`]{#lh:FN15}`DecisionQuotient.BayesOptimalityProof.KL_eq_sum_klFun`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FN16`]{#lh:FN16}`DecisionQuotient.BayesOptimalityProof.KL_eq_zero_iff_eq`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP1`]{#lh:FP1}`DecisionQuotient.Physics.LocalityPhysics.trivial_states_all_equal`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP2`]{#lh:FP2}`DecisionQuotient.Physics.LocalityPhysics.equal_states_constant_function`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP3`]{#lh:FP3}`DecisionQuotient.Physics.LocalityPhysics.constant_function_singleton_image`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP4`]{#lh:FP4}`DecisionQuotient.Physics.LocalityPhysics.singleton_image_zero_entropy`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP5`]{#lh:FP5}`DecisionQuotient.Physics.LocalityPhysics.zero_entropy_no_information`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP6`]{#lh:FP6}`DecisionQuotient.Physics.LocalityPhysics.triviality_implies_no_information`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP7`]{#lh:FP7}`DecisionQuotient.Physics.LocalityPhysics.information_requires_nontriviality`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP8`]{#lh:FP8}`DecisionQuotient.Physics.LocalityPhysics.atypical_states_rare`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP9`]{#lh:FP9}`DecisionQuotient.Physics.LocalityPhysics.random_misses_target`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP10`]{#lh:FP10}`DecisionQuotient.Physics.LocalityPhysics.errors_accumulate`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP11`]{#lh:FP11}`DecisionQuotient.Physics.LocalityPhysics.wrong_paths_dominate`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP12`]{#lh:FP12}`DecisionQuotient.Physics.LocalityPhysics.second_law_from_counting`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP13`]{#lh:FP13}`DecisionQuotient.Physics.LocalityPhysics.verification_is_information`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP14`]{#lh:FP14}`DecisionQuotient.Physics.LocalityPhysics.entropy_is_information`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FP15`]{#lh:FP15}`DecisionQuotient.Physics.LocalityPhysics.landauer_structure`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT1`]{#lh:FPT1}`DecisionQuotient.Physics.LocalityPhysics.Timeline`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT2`]{#lh:FPT2}`DecisionQuotient.Physics.LocalityPhysics.FPT2_function_deterministic`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT3`]{#lh:FPT3}`DecisionQuotient.Physics.LocalityPhysics.FPT3_outputs_differ_inputs_differ`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT4`]{#lh:FPT4}`DecisionQuotient.Physics.LocalityPhysics.FPT4_step_requires_distinct_moments`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT5`]{#lh:FPT5}`DecisionQuotient.Physics.LocalityPhysics.FPT5_distinct_moments_positive_duration`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT6`]{#lh:FPT6}`DecisionQuotient.Physics.LocalityPhysics.FPT6_step_takes_positive_time`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT7`]{#lh:FPT7}`DecisionQuotient.Physics.LocalityPhysics.FPT7_no_instantaneous_steps`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT8`]{#lh:FPT8}`DecisionQuotient.Physics.LocalityPhysics.FPT8_propagation_takes_time`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT9`]{#lh:FPT9}`DecisionQuotient.Physics.LocalityPhysics.FPT9_speed_bounded_by_positive_time`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FPT10`]{#lh:FPT10}`DecisionQuotient.Physics.LocalityPhysics.FPT10_ec3_is_logical`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FS1`]{#lh:FS1}`DecisionQuotient.Statistics.sum_fisherScore_eq_srank`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FS2`]{#lh:FS2}`DecisionQuotient.Statistics.fisherMatrix_rank_eq_srank`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FS3`]{#lh:FS3}`DecisionQuotient.Statistics.fisherMatrix_trace_eq_srank`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FS4`]{#lh:FS4}`DecisionQuotient.Statistics.fisherScore_relevant`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`FS5`]{#lh:FS5}`DecisionQuotient.Statistics.fisherScore_irrelevant`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE1`]{#lh:GE1}`DecisionQuotient.ClaimClosure.GE1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE2`]{#lh:GE2}`DecisionQuotient.ClaimClosure.GE2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE3`]{#lh:GE3}`DecisionQuotient.ClaimClosure.GE3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE4`]{#lh:GE4}`DecisionQuotient.ClaimClosure.GE4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE5`]{#lh:GE5}`DecisionQuotient.ClaimClosure.GE5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE6`]{#lh:GE6}`DecisionQuotient.ClaimClosure.GE6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE7`]{#lh:GE7}`DecisionQuotient.ClaimClosure.GE7`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE8`]{#lh:GE8}`DecisionQuotient.ClaimClosure.GE8`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GE9`]{#lh:GE9}`DecisionQuotient.ClaimClosure.GE9`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GEN1`]{#lh:GEN1}`generated_file_is_second_encoding`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN1`]{#lh:GN1}`DecisionQuotient.LogicGraph.isCycle`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN2`]{#lh:GN2}`DecisionQuotient.LogicGraph.cycleWitnessBits_pos`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN3`]{#lh:GN3}`DecisionQuotient.LogicGraph.pathProb_nonneg`                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN4`]{#lh:GN4}`DecisionQuotient.LogicGraph.pathSurprisal_nonneg_of_positive_mass`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN5`]{#lh:GN5}`DecisionQuotient.LogicGraph.nontrivialityScore_unknown`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN6`]{#lh:GN6}`DecisionQuotient.LogicGraph.observerEntropy_nonneg`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN7`]{#lh:GN7}`DecisionQuotient.LogicGraph.dqFromEntropy_in_unit_interval`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN8`]{#lh:GN8}`DecisionQuotient.LogicGraph.path_belief_forced_under_uncertainty`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN9`]{#lh:GN9}`DecisionQuotient.LogicGraph.bayes_update_exists_for_observer_paths`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN10`]{#lh:GN10}`DecisionQuotient.LogicGraph.cycle_witness_implies_positive_landauer`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN11`]{#lh:GN11}`DecisionQuotient.LogicGraph.cycle_witness_implies_positive_nv_work`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN12`]{#lh:GN12}`DecisionQuotient.LogicGraph.dna_erasure_implies_positive_landauer`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`GN13`]{#lh:GN13}`DecisionQuotient.LogicGraph.dna_room_temp_environmental_stability`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD1`]{#lh:HD1}`DecisionQuotient.HardnessDistribution.centralization_dominance_bundle`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD2`]{#lh:HD2}`DecisionQuotient.HardnessDistribution.centralization_step_saves_n_minus_one`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD3`]{#lh:HD3}`DecisionQuotient.HardnessDistribution.centralized_higher_leverage`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD4`]{#lh:HD4}`DecisionQuotient.HardnessDistribution.complete_model_dominates_after_threshold`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD5`]{#lh:HD5}`DecisionQuotient.HardnessDistribution.gap_conservation_card`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD6`]{#lh:HD6}`DecisionQuotient.HardnessDistribution.generalizedTotal_with_saturation_eventually_constant`                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD7`]{#lh:HD7}`DecisionQuotient.HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD8`]{#lh:HD8}`DecisionQuotient.HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD9`]{#lh:HD9}`DecisionQuotient.HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD10`]{#lh:HD10}`DecisionQuotient.HardnessDistribution.generalized_right_eventually_dominates_wrong`                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD11`]{#lh:HD11}`DecisionQuotient.HardnessDistribution.hardnessEfficiency_eq_central_share`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD12`]{#lh:HD12}`DecisionQuotient.HardnessDistribution.isRightHardness`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD13`]{#lh:HD13}`DecisionQuotient.HardnessDistribution.isWrongHardness`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD14`]{#lh:HD14}`DecisionQuotient.HardnessDistribution.linear_lt_exponential_plus_constant_eventually`                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD15`]{#lh:HD15}`DecisionQuotient.HardnessDistribution.native_dominates_manual`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD16`]{#lh:HD16}`DecisionQuotient.HardnessDistribution.no_positive_slope_linear_represents_saturating`                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD17`]{#lh:HD17}`DecisionQuotient.HardnessDistribution.requiredWork`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD18`]{#lh:HD18}`DecisionQuotient.HardnessDistribution.requiredWork_eq_affine_in_sites`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD19`]{#lh:HD19}`DecisionQuotient.HardnessDistribution.right_dominates_wrong`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD20`]{#lh:HD20}`DecisionQuotient.HardnessDistribution.saturatingSiteCost_eventually_constant`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD21`]{#lh:HD21}`DecisionQuotient.HardnessDistribution.simplicityTax_grows`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD22`]{#lh:HD22}`DecisionQuotient.HardnessDistribution.hardnessLowerBound`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD23`]{#lh:HD23}`DecisionQuotient.HardnessDistribution.hardness_is_irreducible_required_work`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD24`]{#lh:HD24}`DecisionQuotient.HardnessDistribution.totalDOF_eventually_constant_iff_zero_distributed`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD25`]{#lh:HD25}`DecisionQuotient.HardnessDistribution.totalDOF_ge_intrinsic`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD26`]{#lh:HD26}`DecisionQuotient.HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD27`]{#lh:HD27}`DecisionQuotient.HardnessDistribution.workGrowthDegree`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HD28`]{#lh:HD28}`DecisionQuotient.HardnessDistribution.workGrowthDegree_zero_iff_eventually_constant`                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HS1`]{#lh:HS1}`DecisionQuotient.Physics.HeisenbergStrong.NoisyPhysicalEncoding`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HS2`]{#lh:HS2}`DecisionQuotient.Physics.HeisenbergStrong.HeisenbergStrongBinding`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HS3`]{#lh:HS3}`DecisionQuotient.Physics.HeisenbergStrong.strong_binding_implies_core_nontrivial`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HS4`]{#lh:HS4}`DecisionQuotient.Physics.HeisenbergStrong.strong_binding_yields_core_encoding_witness`                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HS5`]{#lh:HS5}`DecisionQuotient.Physics.HeisenbergStrong.strong_binding_implies_physical_nontrivial_opt_assumption`            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`HS6`]{#lh:HS6}`DecisionQuotient.Physics.HeisenbergStrong.strong_binding_implies_nontrivial_opt_via_uncertainty`                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA1`]{#lh:IA1}`DecisionQuotient.ClaimClosure.IA1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA2`]{#lh:IA2}`DecisionQuotient.ClaimClosure.IA2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA3`]{#lh:IA3}`DecisionQuotient.ClaimClosure.IA3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA4`]{#lh:IA4}`DecisionQuotient.ClaimClosure.IA4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA5`]{#lh:IA5}`DecisionQuotient.ClaimClosure.IA5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA6`]{#lh:IA6}`DecisionQuotient.ClaimClosure.IA6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA7`]{#lh:IA7}`DecisionQuotient.ClaimClosure.IA7`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA8`]{#lh:IA8}`DecisionQuotient.ClaimClosure.IA8`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA9`]{#lh:IA9}`DecisionQuotient.ClaimClosure.IA9`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA10`]{#lh:IA10}`DecisionQuotient.ClaimClosure.IA10`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA11`]{#lh:IA11}`DecisionQuotient.ClaimClosure.IA11`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA12`]{#lh:IA12}`DecisionQuotient.ClaimClosure.IA12`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IA13`]{#lh:IA13}`DecisionQuotient.ClaimClosure.IA13`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC1`]{#lh:IC1}`DecisionQuotient.IntegrityCompetence.CertaintyInflation`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC2`]{#lh:IC2}`DecisionQuotient.IntegrityCompetence.CompletionFractionDefined`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC3`]{#lh:IC3}`DecisionQuotient.IntegrityCompetence.EvidenceForReport`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC4`]{#lh:IC4}`DecisionQuotient.IntegrityCompetence.ExactCertaintyInflation`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC5`]{#lh:IC5}`DecisionQuotient.IntegrityCompetence.Percent`                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC6`]{#lh:IC6}`DecisionQuotient.IntegrityCompetence.RLFFWeights`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC7`]{#lh:IC7}`DecisionQuotient.IntegrityCompetence.ReportSignal`                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC8`]{#lh:IC8}`DecisionQuotient.IntegrityCompetence.ReportBitModel`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC9`]{#lh:IC9}`DecisionQuotient.IntegrityCompetence.SignalConsistent`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC10`]{#lh:IC10}`DecisionQuotient.IntegrityCompetence.admissible_irrational_strictly_more_than_rational`                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC11`]{#lh:IC11}`DecisionQuotient.IntegrityCompetence.admissible_matrix_counts`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC12`]{#lh:IC12}`DecisionQuotient.IntegrityCompetence.abstain_signal_exists_with_guess_self`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC13`]{#lh:IC13}`DecisionQuotient.IntegrityCompetence.certaintyInflation_iff_not_admissible`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC14`]{#lh:IC14}`DecisionQuotient.IntegrityCompetence.certificationOverheadBits`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC15`]{#lh:IC15}`DecisionQuotient.IntegrityCompetence.certificationOverheadBits_of_evidence`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC16`]{#lh:IC16}`DecisionQuotient.IntegrityCompetence.certificationOverheadBits_of_no_evidence`                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC17`]{#lh:IC17}`DecisionQuotient.IntegrityCompetence.certifiedTotalBits`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC18`]{#lh:IC18}`DecisionQuotient.IntegrityCompetence.certifiedTotalBits_ge_raw`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC19`]{#lh:IC19}`DecisionQuotient.IntegrityCompetence.certifiedTotalBits_gt_raw_of_evidence`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC20`]{#lh:IC20}`DecisionQuotient.IntegrityCompetence.certifiedTotalBits_of_evidence`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC21`]{#lh:IC21}`DecisionQuotient.IntegrityCompetence.certifiedTotalBits_of_no_evidence`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC22`]{#lh:IC22}`DecisionQuotient.IntegrityCompetence.claim_admissible_of_evidence`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC23`]{#lh:IC23}`DecisionQuotient.IntegrityCompetence.competence_implies_integrity`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC24`]{#lh:IC24}`DecisionQuotient.IntegrityCompetence.completion_fraction_defined_of_declared_bound`                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC25`]{#lh:IC25}`DecisionQuotient.IntegrityCompetence.epsilon_competence_implies_integrity`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC26`]{#lh:IC26}`DecisionQuotient.IntegrityCompetence.evidence_nonempty_iff_claim_admissible`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC27`]{#lh:IC27}`DecisionQuotient.IntegrityCompetence.evidence_of_claim_admissible`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC28`]{#lh:IC28}`DecisionQuotient.IntegrityCompetence.exact_claim_admissible_iff_exact_evidence_nonempty`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC29`]{#lh:IC29}`DecisionQuotient.IntegrityCompetence.exact_claim_requires_evidence`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC30`]{#lh:IC30}`DecisionQuotient.IntegrityCompetence.exactCertaintyInflation_iff_no_exact_competence`                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC31`]{#lh:IC31}`DecisionQuotient.IntegrityCompetence.exact_raw_only_of_no_exact_admissible`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC32`]{#lh:IC32}`DecisionQuotient.IntegrityCompetence.integrity_forces_abstention`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC33`]{#lh:IC33}`DecisionQuotient.IntegrityCompetence.integrity_not_competent_of_nonempty_scope`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC34`]{#lh:IC34}`DecisionQuotient.IntegrityCompetence.integrity_resource_bound`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC35`]{#lh:IC35}`DecisionQuotient.IntegrityCompetence.no_completion_fraction_without_declared_bound`                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC36`]{#lh:IC36}`DecisionQuotient.IntegrityCompetence.overModelVerdict_rational_iff`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC37`]{#lh:IC37}`DecisionQuotient.IntegrityCompetence.percentZero`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC38`]{#lh:IC38}`DecisionQuotient.IntegrityCompetence.rlffBaseReward`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC39`]{#lh:IC39}`DecisionQuotient.IntegrityCompetence.rlffReward`                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC40`]{#lh:IC40}`DecisionQuotient.IntegrityCompetence.rlff_abstain_strictly_prefers_no_certificates`                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC41`]{#lh:IC41}`DecisionQuotient.IntegrityCompetence.rlff_maximizer_has_evidence`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC42`]{#lh:IC42}`DecisionQuotient.IntegrityCompetence.rlff_maximizer_is_admissible`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC43`]{#lh:IC43}`DecisionQuotient.IntegrityCompetence.self_reflected_confidence_not_certification`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC44`]{#lh:IC44}`DecisionQuotient.IntegrityCompetence.signal_certified_positive_implies_admissible`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC45`]{#lh:IC45}`DecisionQuotient.IntegrityCompetence.signal_consistent_of_claim_admissible`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC46`]{#lh:IC46}`DecisionQuotient.IntegrityCompetence.signal_no_evidence_forces_zero_certified`                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC47`]{#lh:IC47}`DecisionQuotient.IntegrityCompetence.signal_exact_no_competence_forces_zero_certified`                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC48`]{#lh:IC48}`DecisionQuotient.IntegrityCompetence.steps_run_scalar_always_defined`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC49`]{#lh:IC49}`DecisionQuotient.IntegrityCompetence.steps_run_scalar_falsifiable`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IC50`]{#lh:IC50}`DecisionQuotient.IntegrityCompetence.zero_epsilon_competence_iff_exact`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE1`]{#lh:IE1}`DecisionQuotient.ClaimClosure.IE1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE2`]{#lh:IE2}`DecisionQuotient.ClaimClosure.IE2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE3`]{#lh:IE3}`DecisionQuotient.ClaimClosure.IE3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE4`]{#lh:IE4}`DecisionQuotient.ClaimClosure.IE4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE5`]{#lh:IE5}`DecisionQuotient.ClaimClosure.IE5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE6`]{#lh:IE6}`DecisionQuotient.ClaimClosure.IE6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE7`]{#lh:IE7}`DecisionQuotient.ClaimClosure.IE7`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE8`]{#lh:IE8}`DecisionQuotient.ClaimClosure.IE8`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE9`]{#lh:IE9}`DecisionQuotient.ClaimClosure.IE9`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE10`]{#lh:IE10}`DecisionQuotient.ClaimClosure.IE10`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE11`]{#lh:IE11}`DecisionQuotient.ClaimClosure.IE11`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE12`]{#lh:IE12}`DecisionQuotient.ClaimClosure.IE12`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE13`]{#lh:IE13}`DecisionQuotient.ClaimClosure.IE13`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE14`]{#lh:IE14}`DecisionQuotient.ClaimClosure.IE14`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE15`]{#lh:IE15}`DecisionQuotient.ClaimClosure.IE15`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE16`]{#lh:IE16}`DecisionQuotient.ClaimClosure.IE16`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IE17`]{#lh:IE17}`DecisionQuotient.ClaimClosure.IE17`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN1`]{#lh:IN1}`DecisionQuotient.Physics.Instantiation.Geometry`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN2`]{#lh:IN2}`DecisionQuotient.Physics.Instantiation.Dynamics`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN3`]{#lh:IN3}`DecisionQuotient.Physics.Instantiation.Circuit`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN4`]{#lh:IN4}`DecisionQuotient.Physics.Instantiation.geometry_plus_dynamics_is_circuit`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN5`]{#lh:IN5}`DecisionQuotient.Physics.Instantiation.DecisionInterpretation`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN6`]{#lh:IN6}`DecisionQuotient.Physics.Instantiation.DecisionCircuit`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN7`]{#lh:IN7}`DecisionQuotient.Physics.Instantiation.Molecule`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN8`]{#lh:IN8}`DecisionQuotient.Physics.Instantiation.Reaction`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN9`]{#lh:IN9}`DecisionQuotient.Physics.Instantiation.ReactionOutcome`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN10`]{#lh:IN10}`DecisionQuotient.Physics.Instantiation.MoleculeGeometry`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN11`]{#lh:IN11}`DecisionQuotient.Physics.Instantiation.MoleculeDynamics`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN12`]{#lh:IN12}`DecisionQuotient.Physics.Instantiation.MoleculeCircuit`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN13`]{#lh:IN13}`DecisionQuotient.Physics.Instantiation.MoleculeAsCircuit`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN14`]{#lh:IN14}`DecisionQuotient.Physics.Instantiation.MoleculeAsDecisionCircuit`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN15`]{#lh:IN15}`DecisionQuotient.Physics.Instantiation.molecule_decision_preserves_geometry`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN16`]{#lh:IN16}`DecisionQuotient.Physics.Instantiation.molecule_decision_preserves_dynamics`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN17`]{#lh:IN17}`DecisionQuotient.Physics.Instantiation.asDecisionCircuit`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN18`]{#lh:IN18}`DecisionQuotient.Physics.Instantiation.asDecisionCircuit_preserves_circuit`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN19`]{#lh:IN19}`DecisionQuotient.Physics.Instantiation.Configuration`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN20`]{#lh:IN20}`DecisionQuotient.Physics.Instantiation.EnergyLandscape`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN21`]{#lh:IN21}`DecisionQuotient.Physics.Instantiation.k_Boltzmann`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN22`]{#lh:IN22}`DecisionQuotient.Physics.Instantiation.LandauerBound`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN23`]{#lh:IN23}`DecisionQuotient.Physics.Instantiation.law_objective_schema`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN24`]{#lh:IN24}`DecisionQuotient.Physics.Instantiation.law_opt_eq_feasible_of_gap`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IN25`]{#lh:IN25}`DecisionQuotient.Physics.Instantiation.law_opt_singleton_of_deterministic`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IND1`]{#lh:IND1}`both_requirements_independent`                                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IND2`]{#lh:IND2}`both_requirements_independent'`                                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`INS1`]{#lh:INS1}`Inconsistency.ssot_is_unique_optimum`                                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`INS2`]{#lh:INS2}`Inconsistency.ssot_required`                                                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`INS3`]{#lh:INS3}`Inconsistency.ssot_unique_satisfier`                                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`INS4`]{#lh:INS4}`Inconsistency.resolution_requires_external_choice`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IP1`]{#lh:IP1}`DecisionQuotient.Physics.LocalityPhysics.ec1_can_be_true`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IP2`]{#lh:IP2}`DecisionQuotient.Physics.LocalityPhysics.ec1_independent_of_ec2_ec3`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IP3`]{#lh:IP3}`DecisionQuotient.Physics.LocalityPhysics.ec2_can_be_true`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IP4`]{#lh:IP4}`DecisionQuotient.Physics.LocalityPhysics.ec2_independent_of_ec1_ec3`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IP5`]{#lh:IP5}`DecisionQuotient.Physics.LocalityPhysics.ec3_can_be_true`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IP6`]{#lh:IP6}`DecisionQuotient.Physics.LocalityPhysics.ec3_independent_of_ec1_ec2`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IP7`]{#lh:IP7}`DecisionQuotient.Physics.LocalityPhysics.empirical_claims_mutually_independent`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IT1`]{#lh:IT1}`DecisionQuotient.DecisionProblem.numOptClasses`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IT3`]{#lh:IT3}`DecisionQuotient.quotientEntropy_le_srank_binary`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IT4`]{#lh:IT4}`DecisionQuotient.numOptClasses_le_pow_srank_binary`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IT5`]{#lh:IT5}`DecisionQuotient.nontrivial_bounds_binary`                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IT6`]{#lh:IT6}`DecisionQuotient.nontrivial_implies_srank_pos`                                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV1`]{#lh:IV1}`DecisionQuotient.InteriorVerification.GoalClass`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV2`]{#lh:IV2}`DecisionQuotient.InteriorVerification.InteriorDominanceVerifiable`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV3`]{#lh:IV3}`DecisionQuotient.InteriorVerification.TautologicalSetIdentifiable`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV4`]{#lh:IV4}`DecisionQuotient.InteriorVerification.agreeOnSet`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV5`]{#lh:IV5}`DecisionQuotient.InteriorVerification.interiorParetoDominates`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV6`]{#lh:IV6}`DecisionQuotient.InteriorVerification.interior_certificate_implies_non_rejection`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV7`]{#lh:IV7}`DecisionQuotient.InteriorVerification.interior_dominance_implies_universal_non_rejection`                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV8`]{#lh:IV8}`DecisionQuotient.InteriorVerification.interior_dominance_not_full_sufficiency`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV9`]{#lh:IV9}`DecisionQuotient.InteriorVerification.interior_verification_tractable_certificate`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV10`]{#lh:IV10}`DecisionQuotient.InteriorVerification.not_sufficientOnSet_of_counterexample`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`IV11`]{#lh:IV11}`DecisionQuotient.InteriorVerification.singleton_coordinate_interior_certificate`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LNG1`]{#lh:LNG1}`ClaimClosure.language_realizability_criterion`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP1`]{#lh:LP1}`DecisionQuotient.Physics.LocalityPhysics.SpacetimePoint`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP2`]{#lh:LP2}`DecisionQuotient.Physics.LocalityPhysics.lightCone`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP3`]{#lh:LP3}`DecisionQuotient.Physics.LocalityPhysics.causalPast`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP4`]{#lh:LP4}`DecisionQuotient.Physics.LocalityPhysics.self_in_lightCone`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP5`]{#lh:LP5}`DecisionQuotient.Physics.LocalityPhysics.self_in_causalPast`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP6`]{#lh:LP6}`DecisionQuotient.Physics.LocalityPhysics.LocalRegion`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP7`]{#lh:LP7}`DecisionQuotient.Physics.LocalityPhysics.canObserve`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP8`]{#lh:LP8}`DecisionQuotient.Physics.LocalityPhysics.spacelikeSeparated`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP9`]{#lh:LP9}`DecisionQuotient.Physics.LocalityPhysics.spacelike_disjoint_observation`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP11`]{#lh:LP11}`DecisionQuotient.Physics.LocalityPhysics.LocalConfiguration`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP12`]{#lh:LP12}`DecisionQuotient.Physics.LocalityPhysics.isLocallyValid`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP13`]{#lh:LP13}`DecisionQuotient.Physics.LocalityPhysics.MergeResult`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP14`]{#lh:LP14}`DecisionQuotient.Physics.LocalityPhysics.boardMerge`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP15`]{#lh:LP15}`DecisionQuotient.Physics.LocalityPhysics.independent_configs_can_disagree`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP16`]{#lh:LP16}`DecisionQuotient.Physics.LocalityPhysics.merge_compatible_iff`                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP17`]{#lh:LP17}`DecisionQuotient.Physics.LocalityPhysics.merge_contradiction_iff`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP18`]{#lh:LP18}`DecisionQuotient.Physics.LocalityPhysics.locality_implies_possible_contradiction`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP19`]{#lh:LP19}`DecisionQuotient.Physics.LocalityPhysics.Superposition`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP20`]{#lh:LP20}`DecisionQuotient.Physics.LocalityPhysics.superposition_can_contain_contradictions`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP21`]{#lh:LP21}`DecisionQuotient.Physics.LocalityPhysics.superposition_requires_separation`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP22`]{#lh:LP22}`DecisionQuotient.Physics.LocalityPhysics.bell_separation_is_real`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP23`]{#lh:LP23}`DecisionQuotient.Physics.LocalityPhysics.measurement_is_merge_contradiction`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP24`]{#lh:LP24}`DecisionQuotient.Physics.LocalityPhysics.entanglement_is_shared_origin`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP31`]{#lh:LP31}`DecisionQuotient.Physics.LocalityPhysics.complete_knowledge_requires_all_queries`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP32`]{#lh:LP32}`DecisionQuotient.Physics.LocalityPhysics.finite_energy_constraint`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP33`]{#lh:LP33}`DecisionQuotient.Physics.LocalityPhysics.self_knowledge_impossible_if_insufficient_energy`                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP34`]{#lh:LP34}`DecisionQuotient.Physics.LocalityPhysics.bounded_energy_forces_locality`                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP35`]{#lh:LP35}`DecisionQuotient.Physics.LocalityPhysics.locality_implies_independent_regions`                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP36`]{#lh:LP36}`DecisionQuotient.Physics.LocalityPhysics.independent_regions_imply_possible_contradiction`                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP38`]{#lh:LP38}`DecisionQuotient.Physics.LocalityPhysics.pne_np_necessary_for_physics`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP39`]{#lh:LP39}`DecisionQuotient.Physics.LocalityPhysics.matter_exists_because_pne_np`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP40`]{#lh:LP40}`DecisionQuotient.Physics.LocalityPhysics.physics_is_the_game`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP41`]{#lh:LP41}`DecisionQuotient.Physics.LocalityPhysics.without_positive_query_cost_no_bound`                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP42`]{#lh:LP42}`DecisionQuotient.Physics.LocalityPhysics.without_nontrivial_states_no_disagreement`                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP43`]{#lh:LP43}`DecisionQuotient.Physics.LocalityPhysics.without_separation_no_independence`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP44`]{#lh:LP44}`DecisionQuotient.Physics.LocalityPhysics.without_finite_capacity_no_gap`                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP45`]{#lh:LP45}`DecisionQuotient.Physics.LocalityPhysics.all_premises_used`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP46`]{#lh:LP46}`DecisionQuotient.Physics.LocalityPhysics.premises_necessary_and_sufficient`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP50`]{#lh:LP50}`DecisionQuotient.Physics.LocalityPhysics.shannon_value_is_intractability`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP51`]{#lh:LP51}`DecisionQuotient.Physics.LocalityPhysics.economic_value_requires_scarcity`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP52`]{#lh:LP52}`DecisionQuotient.Physics.LocalityPhysics.thermodynamic_value_requires_gradient`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP53`]{#lh:LP53}`DecisionQuotient.Physics.LocalityPhysics.voi_requires_uncertainty`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP54`]{#lh:LP54}`DecisionQuotient.Physics.LocalityPhysics.physics_requires_intractability`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP55`]{#lh:LP55}`DecisionQuotient.Physics.LocalityPhysics.value_is_intractability`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP56`]{#lh:LP56}`DecisionQuotient.Physics.LocalityPhysics.observers_value_the_intractable`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP57`]{#lh:LP57}`DecisionQuotient.Physics.LocalityPhysics.finite_steps_finite_coverage`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP58`]{#lh:LP58}`DecisionQuotient.Physics.LocalityPhysics.counting_gap`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP59`]{#lh:LP59}`DecisionQuotient.Physics.LocalityPhysics.time_is_counting`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP60`]{#lh:LP60}`DecisionQuotient.Physics.LocalityPhysics.gap_equivalence`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`LP61`]{#lh:LP61}`DecisionQuotient.Physics.LocalityPhysics.light_cone_is_time_gap`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_05a51b10`]{#lh:L_05a51b10}`Leverage.Physical.positive_energy_of_wellformed_arch`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_062d9169`]{#lh:L_062d9169}`Leverage.linear_model_preserves_ordering`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_09703163`]{#lh:L_09703163}`Leverage.correctness_probability`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_0c281f80`]{#lh:L_0c281f80}`Leverage.leverage_caps_principle`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_1aedfdca`]{#lh:L_1aedfdca}`Leverage.error_probability_denom_pos`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_1af867ce`]{#lh:L_1af867ce}`Leverage.Physical.feasible_iff_floor_le_budget`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_1bc009bb`]{#lh:L_1bc009bb}`Leverage.composition_dof_additive`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_1fb0826b`]{#lh:L_1fb0826b}`Leverage.Physical.physical_assumption_necessity_witnesses`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_2027e0f3`]{#lh:L_2027e0f3}`Leverage.SSOT.paper2_leverage_ratio`                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_28e01ed8`]{#lh:L_28e01ed8}`Leverage.max_leverage_is_optimal`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_3432eddd`]{#lh:L_3432eddd}`Leverage.Physical.higher_leverage_same_caps_preserves_feasibility_under_same_budget`              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_3a9932b8`]{#lh:L_3a9932b8}`Leverage.SSOT.modification_ratio`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_3c6b4088`]{#lh:L_3c6b4088}`Leverage.SSOT.paper2_is_leverage_instance`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_4372537d`]{#lh:L_4372537d}`Leverage.Typing.nominal_dominates_duck`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_45cc4f88`]{#lh:L_45cc4f88}`Leverage.leverage_gap`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_48108f64`]{#lh:L_48108f64}`Leverage.SSOT.ssot_leverage_dominance`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_509b7c92`]{#lh:L_509b7c92}`Leverage.composition_caps_additive`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_515d1d9d`]{#lh:L_515d1d9d}`Leverage.Physical.energyLowerBound_eq_joules_times_dof`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_5250a1d9`]{#lh:L_5250a1d9}`Leverage.metaprogramming_dominates`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_54abf361`]{#lh:L_54abf361}`Leverage.modification_eq_dof`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_55494009`]{#lh:L_55494009}`Leverage.testable_modification_prediction`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_55928d9f`]{#lh:L_55928d9f}`Leverage.expected_errors_from_linearity`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_5af424e9`]{#lh:L_5af424e9}`Leverage.leverage_error_tradeoff`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_5b347895`]{#lh:L_5b347895}`Leverage.Physical.lower_dof_lower_energy`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_674e36f4`]{#lh:L_674e36f4}`Leverage.bernoulli_justifies_linear_model`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_70adb6e2`]{#lh:L_70adb6e2}`Leverage.dof_ratio_predicts_error_ratio`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_76f8fb86`]{#lh:L_76f8fb86}`Leverage.isomorphism_preserves_failure_ordering`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_80dff953`]{#lh:L_80dff953}`Leverage.system_is_correct`                                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_917c2f4f`]{#lh:L_917c2f4f}`Leverage.dof_reliability_isomorphism`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_94799bf0`]{#lh:L_94799bf0}`Leverage.error_independence_from_orthogonality`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_9c6279a3`]{#lh:L_9c6279a3}`Leverage.Physical.higher_leverage_same_caps_implies_lower_energy`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_9f6625e0`]{#lh:L_9f6625e0}`Leverage.Typing.paper1_is_leverage_instance`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_a2e95cfd`]{#lh:L_a2e95cfd}`Leverage.Physical.zero_model_energy_is_zero`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_a42f986c`]{#lh:L_a42f986c}`Leverage.optimal_minimizes_error`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_a87ad5d3`]{#lh:L_a87ad5d3}`Leverage.architecture_axes_independent`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_ad7ca324`]{#lh:L_ad7ca324}`Leverage.leverage_maximization_principle`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_b8e54251`]{#lh:L_b8e54251}`Leverage.composition_preserves_leverage_bound`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_bcf5655e`]{#lh:L_bcf5655e}`Leverage.expected_errors_linear`                                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_bf24afdb`]{#lh:L_bf24afdb}`Leverage.lower_dof_lower_errors`                                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_c022ff39`]{#lh:L_c022ff39}`Leverage.metaprogramming_unbounded_leverage`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_c4bbc516`]{#lh:L_c4bbc516}`Leverage.Physical.infeasible_of_budget_lt_floor`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_cd7df084`]{#lh:L_cd7df084}`Leverage.ordering_equivalence_exact`                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_d49a3a6e`]{#lh:L_d49a3a6e}`Leverage.compose_dof`                                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_d6782c96`]{#lh:L_d6782c96}`Leverage.Typing.capability_gap`                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_dbf653bd`]{#lh:L_dbf653bd}`Leverage.Typing.leverage_ratio`                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_e0961ce8`]{#lh:L_e0961ce8}`Leverage.Physical.feasible_budget_exists`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_e8b1c801`]{#lh:L_e8b1c801}`Leverage.isomorphism_roundtrip`                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_ebcd21af`]{#lh:L_ebcd21af}`Leverage.Physical.positive_energy_gap_of_higher_leverage`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_f3216891`]{#lh:L_f3216891}`Leverage.Physical.positive_floor_requires_positive_joules_assumption`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`L_f7d1d766`]{#lh:L_f7d1d766}`Leverage.series_error_probability`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MI1`]{#lh:MI1}`DecisionQuotient.ClaimClosure.MI1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MI2`]{#lh:MI2}`DecisionQuotient.ClaimClosure.MI2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MI3`]{#lh:MI3}`DecisionQuotient.ClaimClosure.MI3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MI4`]{#lh:MI4}`DecisionQuotient.ClaimClosure.MI4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MI5`]{#lh:MI5}`DecisionQuotient.ClaimClosure.MI5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN1`]{#lh:MN1}`DecisionQuotient.Physics.MeasureNecessity.quantitative_claim_has_measure`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN2`]{#lh:MN2}`DecisionQuotient.Physics.MeasureNecessity.stochastic_claim_has_probability_measure`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN3`]{#lh:MN3}`DecisionQuotient.Physics.MeasureNecessity.stochastic_claim_has_measure`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN4`]{#lh:MN4}`DecisionQuotient.Physics.MeasureNecessity.count_univ_bool`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN5`]{#lh:MN5}`DecisionQuotient.Physics.MeasureNecessity.counting_measure_not_probability_on_bool`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN6`]{#lh:MN6}`DecisionQuotient.Physics.MeasureNecessity.deterministic_dirac_is_probability`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN7`]{#lh:MN7}`DecisionQuotient.Physics.MeasureNecessity.quantitative_value_depends_on_measure`                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN8`]{#lh:MN8}`DecisionQuotient.Physics.MeasureNecessity.deterministic_models_still_measure_based`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN9`]{#lh:MN9}`DecisionQuotient.Physics.MeasureNecessity.measure_does_not_imply_probability`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN10`]{#lh:MN10}`DecisionQuotient.Physics.MeasureNecessity.quantitative_measure_is_logical_prerequisite`                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`MN11`]{#lh:MN11}`DecisionQuotient.Physics.MeasureNecessity.stochastic_probability_is_logical_prerequisite`                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR1`]{#lh:OR1}`DecisionQuotient.Physics.ObserverRelativeState.ObserverClass`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR2`]{#lh:OR2}`DecisionQuotient.Physics.ObserverRelativeState.obsEquiv`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR3`]{#lh:OR3}`DecisionQuotient.Physics.ObserverRelativeState.EffectiveStateSpace`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR4`]{#lh:OR4}`DecisionQuotient.Physics.ObserverRelativeState.project_eq_iff`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR5`]{#lh:OR5}`DecisionQuotient.Physics.ObserverRelativeState.observer_relative_equivalence_witness`                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR6`]{#lh:OR6}`DecisionQuotient.Physics.ObserverRelativeState.PhysicalObserverClass`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR7`]{#lh:OR7}`DecisionQuotient.Physics.ObserverRelativeState.PhysicalStateSpace`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR8`]{#lh:OR8}`DecisionQuotient.Physics.ObserverRelativeState.physical_state_space_has_instance_witness`                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`OR9`]{#lh:OR9}`DecisionQuotient.Physics.ObserverRelativeState.physical_observer_relative_effective_space`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`ORA1`]{#lh:ORA1}`oracle_arbitrary`                                                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA1`]{#lh:PA1}`DecisionQuotient.Physics.AnchorChecks.obsEquiv_all_of_effective_subsingleton`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA2`]{#lh:PA2}`DecisionQuotient.Physics.AnchorChecks.stochasticAnchorSufficient_iff_exists_anchor_singleton`                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA3`]{#lh:PA3}`DecisionQuotient.Physics.AnchorChecks.stochastic_anchor_check_iff_exists_anchor_singleton`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA4`]{#lh:PA4}`DecisionQuotient.Physics.AnchorChecks.stochastic_sufficient_of_observer_collapse_and_seed`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA5`]{#lh:PA5}`DecisionQuotient.Physics.AnchorChecks.stochastic_anchor_check_of_observer_collapse_and_seed`                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA6`]{#lh:PA6}`DecisionQuotient.Physics.AnchorChecks.sequential_sufficient_of_observer_collapse`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA7`]{#lh:PA7}`DecisionQuotient.Physics.AnchorChecks.sequential_anchor_check_of_observer_collapse`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA8`]{#lh:PA8}`DecisionQuotient.Physics.AnchorChecks.physical_observer_collapse_implies_obsEquiv_all`                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PA9`]{#lh:PA9}`DecisionQuotient.Physics.AnchorChecks.physical_stochastic_anchor_check_of_observer_collapse_and_seed`           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC1`]{#lh:PBC1}`DecisionQuotient.PhysicalBudgetCrossover.CrossoverAt`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC2`]{#lh:PBC2}`DecisionQuotient.PhysicalBudgetCrossover.SuccinctInfeasible`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC3`]{#lh:PBC3}`DecisionQuotient.PhysicalBudgetCrossover.SuccinctUnbounded`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC4`]{#lh:PBC4}`DecisionQuotient.PhysicalBudgetCrossover.explicit_infeasible_succinct_feasible_of_crossover`                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC5`]{#lh:PBC5}`DecisionQuotient.PhysicalBudgetCrossover.exists_least_crossover_point`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC6`]{#lh:PBC6}`DecisionQuotient.PhysicalBudgetCrossover.has_crossover_of_bounded_succinct_unbounded_explicit`                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC7`]{#lh:PBC7}`DecisionQuotient.PhysicalBudgetCrossover.explicit_eventual_infeasibility_of_monotone_and_witness`             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC8`]{#lh:PBC8}`DecisionQuotient.PhysicalBudgetCrossover.crossover_eventually_of_eventual_split`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC9`]{#lh:PBC9}`DecisionQuotient.PhysicalBudgetCrossover.payoff_threshold_explicit_vs_succinct`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC10`]{#lh:PBC10}`DecisionQuotient.PhysicalBudgetCrossover.no_universal_survivor_without_succinct_bound`                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC11`]{#lh:PBC11}`DecisionQuotient.PhysicalBudgetCrossover.policy_closure_at_divergence`                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PBC12`]{#lh:PBC12}`DecisionQuotient.PhysicalBudgetCrossover.policy_closure_beyond_divergence`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH1`]{#lh:PH1}`PhysicalComplexity.k_Boltzmann`                                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH2`]{#lh:PH2}`PhysicalComplexity.PhysicalComputer`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH3`]{#lh:PH3}`PhysicalComplexity.bit_energy_cost`                                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH4`]{#lh:PH4}`PhysicalComplexity.Landauer_bound`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH5`]{#lh:PH5}`PhysicalComplexity.InstanceSize`                                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH6`]{#lh:PH6}`PhysicalComplexity.ComputationalRequirement`                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH7`]{#lh:PH7}`PhysicalComplexity.coNP_requirement`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH8`]{#lh:PH8}`PhysicalComplexity.coNP_physically_impossible`                                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH9`]{#lh:PH9}`PhysicalComplexity.coNP_not_in_P_physically`                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH10`]{#lh:PH10}`PhysicalComplexity.sufficiency_physically_impossible`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH11`]{#lh:PH11}`DecisionQuotient.PhysicalComplexity.PhysicalCollapseAtRequirement`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH12`]{#lh:PH12}`DecisionQuotient.PhysicalComplexity.no_physical_collapse_at_requirement`                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH13`]{#lh:PH13}`DecisionQuotient.PhysicalComplexity.canonical_physical_collapse_impossible`                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH14`]{#lh:PH14}`DecisionQuotient.PhysicalComplexity.p_eq_np_physically_impossible_of_collapse_map`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH15`]{#lh:PH15}`DecisionQuotient.PhysicalComplexity.p_eq_np_physically_impossible_canonical`                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH16`]{#lh:PH16}`DecisionQuotient.PhysicalComplexity.P_eq_NP_via_SAT`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH17`]{#lh:PH17}`DecisionQuotient.PhysicalComplexity.SAT3ReductionBridge`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH18`]{#lh:PH18}`DecisionQuotient.PhysicalComplexity.sat_reduction_transfers_energy_lower_bound`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH19`]{#lh:PH19}`DecisionQuotient.PhysicalComplexity.physical_collapse_of_polytime_sat_realization`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH20`]{#lh:PH20}`DecisionQuotient.PhysicalComplexity.p_eq_np_physically_impossible_via_sat_bridge`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH21`]{#lh:PH21}`DecisionQuotient.PhysicalComplexity.SAT3HardFamily`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH22`]{#lh:PH22}`DecisionQuotient.PhysicalComplexity.p_eq_np_physically_impossible_via_sat_hard_family`                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH23`]{#lh:PH23}`DecisionQuotient.PhysicalComplexity.collapse_possible_without_positive_bit_cost`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH24`]{#lh:PH24}`DecisionQuotient.PhysicalComplexity.collapse_possible_without_exponential_lower_bound`                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH25`]{#lh:PH25}`DecisionQuotient.PhysicalComplexity.no_go_transfer_requires_collapse_map`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH26`]{#lh:PH26}`DecisionQuotient.PhysicalComplexity.no_collapse_of_bounded_budget_pos_cost_exp_lb`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH27`]{#lh:PH27}`DecisionQuotient.PhysicalComplexity.collapse_implies_assumption_failure_disjunction`                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH28`]{#lh:PH28}`DecisionQuotient.PhysicalComplexity.deterministic_no_physical_collapse`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH29`]{#lh:PH29}`DecisionQuotient.PhysicalComplexity.probabilistic_no_physical_collapse`                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH30`]{#lh:PH30}`DecisionQuotient.PhysicalComplexity.sequential_no_physical_collapse`                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH31`]{#lh:PH31}`DecisionQuotient.PhysicalComplexity.collapse_possible_with_unbounded_budget_profile`                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH32`]{#lh:PH32}`DecisionQuotient.PhysicalComplexity.exp_budget_profile_unbounded`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH33`]{#lh:PH33}`DecisionQuotient.PhysicalComplexity.finite_budget_assumption_is_necessary`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH34`]{#lh:PH34}`DecisionQuotient.PhysicalComplexity.CoherentDQRejectionAtRequirement`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH35`]{#lh:PH35}`DecisionQuotient.PhysicalComplexity.coherent_dq_rejection_impossible_at_requirement`                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PH36`]{#lh:PH36}`DecisionQuotient.PhysicalComplexity.coherent_dq_rejection_impossible_canonical`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PI1`]{#lh:PI1}`DecisionQuotient.Physics.PhysicalIncompleteness.UniverseModel`                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PI2`]{#lh:PI2}`DecisionQuotient.Physics.PhysicalIncompleteness.PhysicallyInstantiated`                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PI3`]{#lh:PI3}`DecisionQuotient.Physics.PhysicalIncompleteness.no_surjective_instantiation_of_card_gap`                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PI4`]{#lh:PI4}`DecisionQuotient.Physics.PhysicalIncompleteness.physical_incompleteness_of_card_gap`                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PI5`]{#lh:PI5}`DecisionQuotient.Physics.PhysicalIncompleteness.physical_incompleteness_of_bounds`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PI6`]{#lh:PI6}`DecisionQuotient.Physics.PhysicalIncompleteness.under_resolution_implies_collision`                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PI7`]{#lh:PI7}`DecisionQuotient.Physics.PhysicalIncompleteness.under_resolution_implies_decision_collision`                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PS1`]{#lh:PS1}`DecisionQuotient.Physics.ClaimTransport.PhysicalStateSemantics`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PS2`]{#lh:PS2}`DecisionQuotient.Physics.ClaimTransport.physical_state_has_witness`                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PS3`]{#lh:PS3}`DecisionQuotient.Physics.ClaimTransport.physical_state_claim_of_instance_claim`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PS4`]{#lh:PS4}`DecisionQuotient.Physics.ClaimTransport.physical_state_claim_of_universal_core`                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PYH1`]{#lh:PYH1}`Python.python_has_hooks`                                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`PYI1`]{#lh:PYI1}`Python.python_has_introspection`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`QT1`]{#lh:QT1}`DecisionQuotient.DecisionProblem.quotient_is_coarsest`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`QT2`]{#lh:QT2}`DecisionQuotient.DecisionProblem.quotientMap_preservesOpt`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`QT3`]{#lh:QT3}`DecisionQuotient.DecisionProblem.quotient_represents_opt_equiv`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`QT4`]{#lh:QT4}`DecisionQuotient.DecisionProblem.factors_implies_respects`                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RAT1`]{#lh:RAT1}`ClaimClosure.rate_incoherence_step`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RD1`]{#lh:RD1}`DecisionQuotient.Information.shannonEntropy_nonneg`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RD2`]{#lh:RD2}`DecisionQuotient.Information.rate_zero_distortion`                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RD3`]{#lh:RD3}`DecisionQuotient.Information.rate_monotone`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RED1`]{#lh:RED1}`ClaimClosure.redundancy_incoherence_equiv`                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`REG1`]{#lh:REG1}`ClaimClosure.operating_regimes_partition`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`REG2`]{#lh:REG2}`ClaimClosure.pareto_optimality_p1`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`REG3`]{#lh:REG3}`ClaimClosure.no_tradeoff_at_p1`                                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`REG4`]{#lh:REG4}`ClaimClosure.amortized_complexity_core`                                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`REQ1`]{#lh:REQ1}`structural_facts_fixed_at_definition`                                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`REQ2`]{#lh:REQ2}`definition_hooks_necessary`                                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`REQ3`]{#lh:REQ3}`introspection_necessary_for_verification`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RS1`]{#lh:RS1}`DecisionQuotient.Information.equiv_preserves_decision`                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RS2`]{#lh:RS2}`DecisionQuotient.Information.rate_equals_srank`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RS3`]{#lh:RS3}`DecisionQuotient.Information.compression_below_srank_fails`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RS4`]{#lh:RS4}`DecisionQuotient.Information.srank_bits_sufficient`                                                             |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`RS5`]{#lh:RS5}`DecisionQuotient.Information.rate_distortion_bridge`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P1`]{#lh:S2P1}`DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P2`]{#lh:S2P2}`DecisionQuotient.Sigma2PHardness.min_representationGap_zero_iff_relevant_card`                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P3`]{#lh:S2P3}`DecisionQuotient.Sigma2PHardness.min_sufficient_set_iff_relevant_card`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P4`]{#lh:S2P4}`DecisionQuotient.Sigma2PHardness.representationGap`                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P5`]{#lh:S2P5}`DecisionQuotient.Sigma2PHardness.representationGap_eq_waste_plus_missing`                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P6`]{#lh:S2P6}`DecisionQuotient.Sigma2PHardness.representationGap_eq_zero_iff`                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P7`]{#lh:S2P7}`DecisionQuotient.Sigma2PHardness.representationGap_missing_eq_gapCard`                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P8`]{#lh:S2P8}`DecisionQuotient.Sigma2PHardness.representationGap_zero_iff_minimalSufficient`                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`S2P9`]{#lh:S2P9}`DecisionQuotient.Sigma2PHardness.sufficient_iff_relevant_subset`                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SE1`]{#lh:SE1}`DecisionQuotient.ClaimClosure.SE1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SE2`]{#lh:SE2}`DecisionQuotient.ClaimClosure.SE2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SE3`]{#lh:SE3}`DecisionQuotient.ClaimClosure.SE3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SE4`]{#lh:SE4}`DecisionQuotient.ClaimClosure.SE4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SE5`]{#lh:SE5}`DecisionQuotient.ClaimClosure.SE5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SE6`]{#lh:SE6}`DecisionQuotient.ClaimClosure.SE6`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SID1`]{#lh:SID1}`ClaimClosure.dof1_zero_side_information`                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SID2`]{#lh:SID2}`ClaimClosure.side_information_scales_with_redundancy`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SOT1`]{#lh:SOT1}`ssot_iff`                                                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SR1`]{#lh:SR1}`DecisionQuotient.ClaimClosure.SR1`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SR2`]{#lh:SR2}`DecisionQuotient.ClaimClosure.SR2`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SR3`]{#lh:SR3}`DecisionQuotient.ClaimClosure.SR3`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SR4`]{#lh:SR4}`DecisionQuotient.ClaimClosure.SR4`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`SR5`]{#lh:SR5}`DecisionQuotient.ClaimClosure.SR5`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC1`]{#lh:TC1}`DecisionQuotient.ToolCollapse.WorkProfile`                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC2`]{#lh:TC2}`DecisionQuotient.ToolCollapse.WorkModel`                                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC3`]{#lh:TC3}`DecisionQuotient.ToolCollapse.ToolModel`                                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC4`]{#lh:TC4}`DecisionQuotient.ToolCollapse.EventualStrictImprovement`                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC5`]{#lh:TC5}`DecisionQuotient.ToolCollapse.EffectiveCollapse`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC6`]{#lh:TC6}`DecisionQuotient.ToolCollapse.tool_never_worse`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC7`]{#lh:TC7}`DecisionQuotient.ToolCollapse.strict_improvement_has_witness`                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC8`]{#lh:TC8}`DecisionQuotient.ToolCollapse.effective_collapse_of_eventual_strict`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC9`]{#lh:TC9}`DecisionQuotient.ToolCollapse.expBaseline`                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC10`]{#lh:TC10}`DecisionQuotient.ToolCollapse.linearTool`                                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC11`]{#lh:TC11}`DecisionQuotient.ToolCollapse.linear_tool_eventual_strict`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TC12`]{#lh:TC12}`DecisionQuotient.ToolCollapse.linear_tool_effective_collapse`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TL3`]{#lh:TL3}`DecisionQuotient.ThermodynamicLift.joulesPerBit_pos_of_landauer_calibration`                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TL4`]{#lh:TL4}`DecisionQuotient.ThermodynamicLift.energy_lower_mandatory_of_landauer_calibration`                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TUR1`]{#lh:TUR1}`DecisionQuotient.Physics.transitionProb_nonneg`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TUR2`]{#lh:TUR2}`DecisionQuotient.Physics.transitionProb_sum_one`                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TUR5`]{#lh:TUR5}`DecisionQuotient.Physics.tur_bridge`                                                                          |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`TUR6`]{#lh:TUR6}`DecisionQuotient.Physics.multiple_futures_entropy_production`                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO1`]{#lh:UO1}`DecisionQuotient.UniverseDynamics`                                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO2`]{#lh:UO2}`DecisionQuotient.feasibleActions`                                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO3`]{#lh:UO3}`DecisionQuotient.lawDecisionProblem`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO4`]{#lh:UO4}`DecisionQuotient.lawUtility`                                                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO5`]{#lh:UO5}`DecisionQuotient.logicallyDeterministic`                                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO6`]{#lh:UO6}`DecisionQuotient.universe_sets_objective_schema`                                                                |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO7`]{#lh:UO7}`DecisionQuotient.lawUtility_eq_of_allowed_iff`                                                                  |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO8`]{#lh:UO8}`DecisionQuotient.opt_eq_feasible_of_gap`                                                                        |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO9`]{#lh:UO9}`DecisionQuotient.infeasible_not_optimal_of_gap`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO10`]{#lh:UO10}`DecisionQuotient.opt_singleton_of_logicallyDeterministic`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UO11`]{#lh:UO11}`DecisionQuotient.opt_eq_of_allowed_iff`                                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UQ1`]{#lh:UQ1}`DecisionQuotient.Physics.Uncertainty.binaryIdentityProblem`                                                     |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UQ2`]{#lh:UQ2}`DecisionQuotient.Physics.Uncertainty.binaryIdentityProblem_opt_true`                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UQ3`]{#lh:UQ3}`DecisionQuotient.Physics.Uncertainty.binaryIdentityProblem_opt_false`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UQ4`]{#lh:UQ4}`DecisionQuotient.Physics.Uncertainty.exists_decision_problem_with_nontrivial_opt`                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UQ5`]{#lh:UQ5}`DecisionQuotient.Physics.Uncertainty.PhysicalNontrivialOptAssumption`                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`UQ6`]{#lh:UQ6}`DecisionQuotient.Physics.Uncertainty.exists_decision_problem_with_nontrivial_opt_of_physical`                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`W1`]{#lh:W1}`DecisionQuotient.Physics.single_future_zero_cost`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`W2`]{#lh:W2}`DecisionQuotient.Physics.transportCost_pos_of_offDiag`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`W3`]{#lh:W3}`DecisionQuotient.Physics.integrity_is_centroid`                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`W4`]{#lh:W4}`DecisionQuotient.Physics.wasserstein_bridge`                                                                      |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`WD1`]{#lh:WD1}`DecisionQuotient.checking_witnessing_duality_budget`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`WD2`]{#lh:WD2}`DecisionQuotient.no_sound_checker_below_witness_budget`                                                         |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`WD3`]{#lh:WD3}`DecisionQuotient.checking_time_ge_witness_budget`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`WD4`]{#lh:WD4}`DecisionQuotient.witnessBudgetEmpty`                                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`WD5`]{#lh:WD5}`DecisionQuotient.checkingBudgetPairs`                                                                           |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`XC1`]{#lh:XC1}`DecisionQuotient.Physics.srank_determines_states`                                                               |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`XC2`]{#lh:XC2}`DecisionQuotient.Physics.more_states_more_transport`                                                            |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`XC3`]{#lh:XC3}`DecisionQuotient.Physics.transport_lower_bound`                                                                 |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`XC4`]{#lh:XC4}`DecisionQuotient.Physics.transport_independent_of_energy`                                                       |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`XC5`]{#lh:XC5}`DecisionQuotient.Physics.transport_independent_of_precision`                                                    |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`XC6`]{#lh:XC6}`DecisionQuotient.Physics.srank_unified_complexity`                                                              |
+----------------------------------------------------------------------------------------------------------------------------------+
| [`XC7`]{#lh:XC7}`DecisionQuotient.Physics.complete_bridge_set`                                                                   |
+----------------------------------------------------------------------------------------------------------------------------------+


  ---------------------------------------------------------------------------------------------------------------------------------------
  **Paper handle**                      **Hardness profile**   **Regime tags**           **Lean support**
  ------------------------------------- ---------------------- ------------------------- ------------------------------------------------
  `cor:dof-errors`                      `unspecified`          \-                        L_a87ad5d3, L_94799bf0

  `cor:dof-monotone`                    `unspecified`          \-                        L_bf24afdb

  `cor:dof-ratio`                       `unspecified`          \-                        L_70adb6e2

  `cor:leverage-energy`                 `unspecified`          \-                        L_9c6279a3, L_ebcd21af

  `cor:linear-approx`                   `unspecified`          \-                        L_674e36f4, L_cd7df084

  `cor:physical-assumption-necessity`   `unspecified`          \-                        L_e0961ce8, L_1fb0826b, L_f3216891, L_a2e95cfd

  `prop:dof-additive`                   `unspecified`          \-                        L_d49a3a6e, L_1bc009bb

  `thm:approx-bound`                    `unspecified`          \-                        L_062d9169, L_cd7df084

  `thm:composition`                     `unspecified`          \-                        L_509b7c92, L_1bc009bb, L_b8e54251

  `thm:dof-reliability`                 `unspecified`          \-                        L_917c2f4f, L_76f8fb86, L_e8b1c801

  `thm:error-compound`                  `unspecified`          \-                        L_09703163, L_80dff953

  `thm:error-independence`              `unspecified`          \-                        L_94799bf0

  `thm:error-prob`                      `unspecified`          \-                        L_1aedfdca, L_f7d1d766

  `thm:expected-errors`                 `unspecified`          \-                        L_55928d9f, L_bcf5655e

  `thm:five-way`                        `unspecified`          \-                        *(no derived Lean handle found)*

  `thm:leverage-error`                  `unspecified`          \-                        L_5af424e9

  `thm:leverage-gap`                    `unspecified`          \-                        L_45cc4f88

  `thm:leverage-max`                    `unspecified`          \-                        L_0c281f80, L_ad7ca324

  `thm:metaprog`                        `unspecified`          \-                        L_5250a1d9, L_c022ff39

  `thm:mod-bound`                       `unspecified`          \-                        L_54abf361

  `thm:nominal-leverage`                `unspecified`          \-                        L_d6782c96, L_dbf653bd, L_4372537d

  `thm:optimal`                         `unspecified`          \-                        L_28e01ed8, L_a42f986c

  `thm:paper1-integration`              `unspecified`          \-                        L_4372537d, L_9f6625e0

  `thm:paper2-integration`              `unspecified`          \-                        L_3c6b4088, L_48108f64

  `thm:physical-budget-boundary`        `unspecified`          \-                        L_1af867ce, L_3432eddd, L_c4bbc516

  `thm:physical-energy-floor`           `unspecified`          \-                        L_515d1d9d, L_5b347895, L_05a51b10

  `thm:ssot-leverage`                   `unspecified`          \-                        L_3a9932b8, L_2027e0f3, L_48108f64

  `thm:testable-prediction`             `unspecified`          \-                        L_55494009
  ---------------------------------------------------------------------------------------------------------------------------------------

*Auto summary: indexed 28 claims by hardness profile (unspecified=28).*


# Notes on assumptions and extensions {#appendix-assumptions}

This appendix lists the principal modeling assumptions and common extensions relevant when applying the leverage framework:

-   **Independence and orthogonality:** Error-independence at the DOF level is derived from axis orthogonality assumptions; when dependencies are present, leverage remains a useful comparative metric but probabilistic models should be adjusted to account for correlation.

-   **Capability counting:** The core theorems require only relative ordering of capabilities; cardinality serves as a practical proxy for capability breadth in examples and case studies.

-   **Multi-objective concerns:** Leverage addresses error probability specifically. Performance, security, and other attributes require multi-objective analysis (e.g., Pareto frontiers) before operational decisions.

-   **Implementations:** SSOT and other instantiations depend on language and platform features; the theoretical principle is implementation-agnostic.

-   **Future work:** Extensions include explicit correlated-error models, weighted capability measures, and integration into multi-criteria architectural decision frameworks.


# Complete Theorem Index {#appendix-theorems}

Paper-level labeled claims in this manuscript:

**Foundations (Section 2):**

-   Proposition [\[prop:dof-additive\]](#prop:dof-additive){reference-type="ref" reference="prop:dof-additive"} (DOF Additivity)

-   Theorem [\[thm:mod-bound\]](#thm:mod-bound){reference-type="ref" reference="thm:mod-bound"} (Modification Bounded by DOF)

**Probability Model (Section 3):**

-   Theorem [\[thm:error-independence\]](#thm:error-independence){reference-type="ref" reference="thm:error-independence"}

-   Corollary [\[cor:dof-errors\]](#cor:dof-errors){reference-type="ref" reference="cor:dof-errors"}

-   Theorem [\[thm:error-compound\]](#thm:error-compound){reference-type="ref" reference="thm:error-compound"}

-   Theorem [\[thm:error-prob\]](#thm:error-prob){reference-type="ref" reference="thm:error-prob"}

-   Corollary [\[cor:linear-approx\]](#cor:linear-approx){reference-type="ref" reference="cor:linear-approx"}

-   Corollary [\[cor:dof-monotone\]](#cor:dof-monotone){reference-type="ref" reference="cor:dof-monotone"}

-   Theorem [\[thm:expected-errors\]](#thm:expected-errors){reference-type="ref" reference="thm:expected-errors"}

-   Theorem [\[thm:dof-reliability\]](#thm:dof-reliability){reference-type="ref" reference="thm:dof-reliability"}

-   Theorem [\[thm:approx-bound\]](#thm:approx-bound){reference-type="ref" reference="thm:approx-bound"}

-   Theorem [\[thm:leverage-gap\]](#thm:leverage-gap){reference-type="ref" reference="thm:leverage-gap"}

-   Theorem [\[thm:testable-prediction\]](#thm:testable-prediction){reference-type="ref" reference="thm:testable-prediction"}

-   Corollary [\[cor:dof-ratio\]](#cor:dof-ratio){reference-type="ref" reference="cor:dof-ratio"}

**Main Results (Section 4):**

-   Theorem [\[thm:leverage-max\]](#thm:leverage-max){reference-type="ref" reference="thm:leverage-max"}

-   Theorem [\[thm:leverage-error\]](#thm:leverage-error){reference-type="ref" reference="thm:leverage-error"}

-   Theorem [\[thm:physical-energy-floor\]](#thm:physical-energy-floor){reference-type="ref" reference="thm:physical-energy-floor"}

-   Corollary [\[cor:leverage-energy\]](#cor:leverage-energy){reference-type="ref" reference="cor:leverage-energy"}

-   Theorem [\[thm:physical-budget-boundary\]](#thm:physical-budget-boundary){reference-type="ref" reference="thm:physical-budget-boundary"}

-   Corollary [\[cor:physical-assumption-necessity\]](#cor:physical-assumption-necessity){reference-type="ref" reference="cor:physical-assumption-necessity"}

-   Theorem [\[thm:metaprog\]](#thm:metaprog){reference-type="ref" reference="thm:metaprog"}

-   Theorem [\[thm:optimal\]](#thm:optimal){reference-type="ref" reference="thm:optimal"}

-   Theorem [\[thm:composition\]](#thm:composition){reference-type="ref" reference="thm:composition"}

-   Theorem [\[thm:paper1-integration\]](#thm:paper1-integration){reference-type="ref" reference="thm:paper1-integration"}

-   Theorem [\[thm:paper2-integration\]](#thm:paper2-integration){reference-type="ref" reference="thm:paper2-integration"}

**Instances (Section 5):**

-   Theorem [\[thm:ssot-leverage\]](#thm:ssot-leverage){reference-type="ref" reference="thm:ssot-leverage"}

-   Theorem [\[thm:nominal-leverage\]](#thm:nominal-leverage){reference-type="ref" reference="thm:nominal-leverage"}

**Mechanization status:** 3691 lines, 201 theorems/lemmas, 0 `sorry`, 14 files.

**Primary Lean sources:**

-   `Leverage/Foundations.lean`

-   `Leverage/Probability.lean`

-   `Leverage/Theorems.lean`

-   `Leverage/Physical.lean`

-   `Leverage/SSOT.lean`

-   `Leverage/Typing.lean`

-   `Leverage/Examples.lean`

-   `Leverage/WeightedLeverage.lean`

-   `LambdaDR.lean`

-   `Leverage.lean`




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper3_leverage/proofs/`
- Lines: 3691
- Theorems: 201
- `sorry` placeholders: 0
