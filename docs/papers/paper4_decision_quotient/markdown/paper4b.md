# Paper: Stochastic and Sequential Regimes: Extending the Decision Quotient to Dynamic Information Sufficiency

**Status**: Draft-ready | **Lean**: 3288 lines, 124 theorems

---

## Abstract

We extend the static decision quotient framework of Paper 4 to stochastic and sequential regimes. Given a decision problem with actions $A$, factored state space $S = X_1 \times \cdots \times X_n$, and utility $U$, we ask: what complexity is required to identify sufficient coordinate sets when (a) the state is drawn from a distribution $P$, or (b) decisions unfold over time with transitions and observations?

**Results:**

-   **Stochastic regime**: STOCHASTIC-SUFFICIENCY-CHECK is PP-complete via MAJSAT reduction. Tractable under product distributions, bounded support, log-concave.

-   **Sequential regime**: SEQUENTIAL-SUFFICIENCY-CHECK is PSPACE-complete via TQBF reduction. Tractable under full observability, bounded horizon, tree structure.

-   **Regime hierarchy**: Static $\subset$ Stochastic $\subset$ Sequential; coNP $\subset$ PP $\subset$ PSPACE.

-   **Substrate cost**: The integrity-competence verdict is substrate-independent; trajectories diverge based on substrate cost $\kappa$.

-   **Temporal learning**: Bayesian structure detection reduces abstention over time.

-   **Temporal integrity**: Evidence-monotone retractions preserve integrity across sequences.

The reduction constructions are machine-checked in Lean 4 (3288 lines, 124 theorems).

**Keywords:** computational complexity, decision theory, stochastic decision problems, POMDPs, polynomial hierarchy, PSPACE


# Introduction {#sec:introduction}

Consider any decision problem $\mathcal{D}$ with actions $A$ and factored state space $S = X_1 \times \cdots \times X_n$. A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only coordinates in $I$ determines the optimal action: $$s_I = s'_I \implies \operatorname{Opt}(s) = \operatorname{Opt}(s')$$ This is *coordinate sufficiency*---the formalization of *information sufficiency* (whether available information determines the optimal action) over a factored state space.

Paper 4 established that SUFFICIENCY-CHECK is coNP-complete for static decision problems $(A, S, U)$. This paper extends that landscape to two natural extensions: stochastic and sequential regimes.

## Stochastic Regime

When the state is drawn from a distribution $P : \Delta(S)$, sufficiency must account for randomness. We use the distribution-conditional definition: $I$ is stochastically sufficient if $P(s \mid s_I) \otimes U$ determines the same optimal action as $P(s) \otimes U$. This subsumes expected-value sufficiency (where only the first moment matters) and connects to classical sufficient statistics.

::: center
  **Regime**   **Tuple**           **Complexity**
  ------------ ------------------- -------------------------
  Static       $(A, S, U)$         coNP-complete (Paper 4)
  Stochastic   $(A, S, U, P)$      -complete
  Sequential   $(A, S, U, T, O)$   -complete
:::

The upper bound comes from counting satisfying assignments weighted by $P$. The lower bound uses a MAJSAT reduction: given $\varphi$, construct uniform $P$ over $\{0,1\}^n$ and let $U(\text{accept}, s) = \varphi(s)$, $U(\text{reject}, s) = 1/2$. Then $\emptyset$ is stochastically sufficient iff $\mathbb{E}_P[\varphi(s)] \geq 1/2$ or $< 1/2$---i.e., majority of assignments satisfy $\varphi$.

Tractable subcases: product distributions (expected utility decomposes), bounded support ($|\text{supp}(P)| \leq k$), log-concave distributions.

## Sequential Regime

When decisions unfold over time with transitions $T : A \times S \to \Delta(S)$ and observations $O : S \to \Delta(\Omega)$, the problem becomes a POMDP. Sequential sufficiency asks whether observation history restricted to $I$-coordinates determines the optimal policy.

The upper bound follows from Papadimitriou & Tsitsiklis (1987). The lower bound uses TQBF reduction: given $\forall x_1 \exists x_2 \forall x_3 \ldots \varphi$, construct $n$ time steps, adversarial transitions at universal quantifiers, agent choices at existential quantifiers, terminal utility $\varphi$. Then full observation history is sequentially sufficient iff the QBF is true.

Tractable subcases: fully observable (MDP), bounded horizon, tree-structured transitions, deterministic transitions.

## Substrate Cost

We extend Paper 4's integrity-competence matrix with substrate cost $\kappa(\text{cell}, \text{agentType})$. The matrix verdict is substrate-independent: $\text{verdict}(c)$ is the same for all agent types. But trajectories diverge: $\text{trajectory}(\sigma, \tau_1) \neq \text{trajectory}(\sigma, \tau_2)$ in general. This is the minimal formal hook for substrate in decision theory.

## Temporal Learning

An agent facing sequential problem instances drawn from unknown distribution $D$ can learn the structure class via Bayesian updates. As $k \to \infty$, posterior $P(C \mid I_1, \ldots, I_k) \to \delta_{C*}$ if structure classes are identifiable. This reduces the abstention frontier: $A_1 \supseteq A_2 \supseteq \ldots$.

## Temporal Integrity

Claims across sequences must satisfy evidence-monotone retractions: an agent retracts a claim only when new evidence contradicts it. Retraction without evidence violates temporal integrity; refinement ($I' \subset I$) is allowed.

## Main Theorems

1.  **Theorem [\[th:stochastic-sufficiency-pp\]](#th:stochastic-sufficiency-pp){reference-type="ref" reference="th:stochastic-sufficiency-pp"}:** STOCHASTIC-SUFFICIENCY-CHECK is -complete via MAJSAT reduction.

2.  **Theorem [\[th:sequential-sufficiency-pspace\]](#th:sequential-sufficiency-pspace){reference-type="ref" reference="th:sequential-sufficiency-pspace"}:** SEQUENTIAL-SUFFICIENCY-CHECK is -complete via TQBF reduction.

3.  **Propositions [\[prop:static-stochastic-strict\]](#prop:static-stochastic-strict){reference-type="ref" reference="prop:static-stochastic-strict"} and [\[prop:stochastic-sequential-strict\]](#prop:stochastic-sequential-strict){reference-type="ref" reference="prop:stochastic-sequential-strict"} (Regime Hierarchy):** Static $\subset$ Stochastic $\subset$ Sequential; coNP$\subset$ $\subset$ .

4.  **Theorem [\[th:substrate-independence-verdict\]](#th:substrate-independence-verdict){reference-type="ref" reference="th:substrate-independence-verdict"} (Substrate Independence of Verdict):** For all cells $c$, $\text{verdict}(c)$ is $\kappa$-independent.

5.  **Theorem [\[th:substrate-dependence-trajectory\]](#th:substrate-dependence-trajectory){reference-type="ref" reference="th:substrate-dependence-trajectory"} (Substrate Dependence of Trajectory):** There exist $\tau_1, \tau_2, \sigma$ with $\text{trajectory}(\sigma, \tau_1) \neq \text{trajectory}(\sigma, \tau_2)$.

## Claim-Typing Bridges (Inherited Static Core)

1.  **Typed claim admissibility (inherited static core):** report admissibility is typed by certificate class ($\mathsf{ABSTAIN}$, $\mathsf{EXACT}$, $\mathsf{EPSILON}(\varepsilon)$).

2.  **Evidence-admissibility equivalence (inherited static core):** first-class evidence-object existence is equivalent to typed report admissibility.

3.  **Empty-sufficient characterization (inherited static core):** the $I=\emptyset$ query is exactly universal constancy of the decision boundary, and non-sufficiency is exactly existence of a counterexample pair.

4.  **Exact requires evidence (inherited static core):** exact admissibility is equivalent to exact evidence existence.

5.  **No evidence implies zero certified confidence (inherited static core):** under signal consistency, no evidence implies zero certified confidence.

\[D:P4-core typed-claim chain; R:DC,AR\]

## Paper Structure

Section [\[sec:stochastic\]](#sec:stochastic){reference-type="ref" reference="sec:stochastic"}: Stochastic decision problems, -completeness, tractable cases. Section [\[sec:sequential\]](#sec:sequential){reference-type="ref" reference="sec:sequential"}: Sequential (POMDP) problems, -completeness, tractable cases. Section [\[sec:regime-hierarchy\]](#sec:regime-hierarchy){reference-type="ref" reference="sec:regime-hierarchy"}: Strict hierarchy of regimes. Section [\[sec:substrate-cost\]](#sec:substrate-cost){reference-type="ref" reference="sec:substrate-cost"}: Substrate cost formalization and independence results. Section [\[sec:temporal-learning\]](#sec:temporal-learning){reference-type="ref" reference="sec:temporal-learning"}: Bayesian structure detection, abstention reduction. Section [\[sec:temporal-integrity\]](#sec:temporal-integrity){reference-type="ref" reference="sec:temporal-integrity"}: Temporal integrity constraints. Section [\[sec:cross-regime-transfer\]](#sec:cross-regime-transfer){reference-type="ref" reference="sec:cross-regime-transfer"}: Transfer conditions between regimes. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"}: Related work.


_Failed to convert 02_stochastic.tex_

_Failed to convert 03_sequential.tex_

# Regime Hierarchy {#sec:regime-hierarchy}

We establish the strict inclusion hierarchy among decision regimes.

::: center
            **Inclusion**            **Complexity Classes**  **Condition**
  --------------------------------- ------------------------ --------------------------------------
     Static $\subset$ Stochastic         coNP$\subset$       Standard assumptions (P $\neq$ coNP)
   Stochastic $\subset$ Sequential         $\subset$         Standard assumptions (P $\neq$ )
:::

::: claim
Strict inclusion static $\subset$ stochasticprop:static-stochastic-strict Under standard complexity assumptions (P $\neq$ coNP), there exist stochastic decision problems that are not statically reducible. \[D:Pprop:static-stochastic-strict; R:P $\neq$ coNP\]
:::

::: claim
Strict inclusion stochastic $\subset$ sequentialprop:stochastic-sequential-strict Under standard complexity assumptions (P $\neq$ ), there exist sequential decision problems that are not stochastically reducible. \[D:Pprop:stochastic-sequential-strict; R:P $\neq$ \]
:::

## Integrity-Resource Bound per Regime

The integrity-resource bound from Paper 4 generalizes to each regime:

1.  **Static** (coNP-hard): polynomial-time agent must abstain on some instances

2.  **Stochastic** (-hard): polynomial-time agent must abstain on MORE instances

3.  **Sequential** (-hard): polynomial-time agent must abstain on EVEN MORE instances

Formally, if $C_1 \subsetneq C_2$ (complexity classes), then the set of instances where integrity forces abstention under $C_1$-resources is a strict superset of those under $C_2$-resources:

$$\{\sigma : \text{integrity forces abstention at } C_1\}
\supsetneq
\{\sigma : \text{integrity forces abstention at } C_2\}$$

::: claim
Abstention frontier shiftsprop:abstention-frontier As regime complexity increases (static $\to$ stochastic $\to$ sequential), the abstention frontier expands. \[D:Pprop:abstention-frontier; R:RG\]
:::

## Regime Detection

A meta-problem: given a problem instance, which regime is it in?

::: decision
[]{#dec:regime-detection label="dec:regime-detection"} **REGIME-DETECTION**: Given a problem instance, is it static, stochastic, or sequential?
:::

Conjecture: regime detection is polynomial for the represented family:

-   Bounded actions $\to$ static

-   Distribution present $\to$ stochastic

-   Transitions/observations present $\to$ sequential


# Substrate Cost {#sec:substrate-cost}

We extend the integrity-competence matrix from Paper 4 with substrate cost $\kappa$.

## Definition

::: definition
[]{#def:substrate-cost label="def:substrate-cost"} $\kappa : (\text{MatrixCell} \times \text{AgentType}) \to (\mathbb{R}_{\ge 0}, \leq)$

Where:

-   MatrixCell = (integrity, attempted, competenceAvailable) triple from Paper 4

-   AgentType = opaque type representing substrate (silicon, carbon, formal system, etc.)

-   The codomain is a totally ordered cost space
:::

::: claim
Verdict is substrate-independentth:substrate-independence-verdict For all cells $c$ and agent types $\tau_1, \tau_2$: $$\text{verdict}(c; \tau_1) = \text{verdict}(c; \tau_2).$$ \[D:Tth:substrate-independence-verdict; R:RG\]
:::

::: claim
Trajectory is substrate-dependentth:substrate-dependence-trajectory There exist agent types $\tau_1, \tau_2$ and problem sequences $\sigma$ such that: $$\text{trajectory}(\sigma; \tau_1) \neq \text{trajectory}(\sigma; \tau_2)$$ even though $\text{verdict}(\sigma_t; \tau_1) = \text{verdict}(\sigma_t; \tau_2)$ for all $t$. \[D:Tth:substrate-dependence-trajectory; R:RG\]
:::

## What $\kappa$ Captures

$\kappa$ is a placeholder for everything the $(A, S, U)$ tuple doesn't model:

-   Memory

-   Motivation

-   Fatigue

-   Identity

-   Embodiment

We do NOT decompose $\kappa$. We acknowledge it exists, show where it enters the dynamics, and prove that the matrix verdict is $\kappa$-independent while the trajectory is $\kappa$-dependent.

::: claim
Minimal formal hookth:substrate-kappa-minimal $\kappa(\text{cell}, \text{agentType})$ is the sufficient statistic of substrate for the trajectory problem. \[D:Tth:substrate-kappa-minimal; R:RG\]
:::

This is the clean separation: the model captures exactly the behaviorally relevant component of substrate, and nothing more.

We do NOT prove that $\kappa$ captures all of subjective experience. We prove that $\kappa$ captures all of subjective experience that is *decision-relevant*---i.e., that affects the agent's trajectory through the problem sequence.

## Where Substrate Enters

The matrix verdict is computed from (integrity, attempted, competenceAvailable). None of these depend on substrate. The verdict is universal.

Substrate enters at exactly one point: the COST of being in a cell. This cost determines:

-   Whether the agent attempts the next instance or rests

-   How the agent allocates resources across a sequence

-   The agent's effective learning rate (some substrates learn faster)

-   The agent's abstention threshold (some substrates tolerate uncertainty better)

This connects to Paper 5 (Credibility): $\kappa = \kappa_{\text{compute}} + \kappa_{\text{communicate}}$, where $\kappa_{\text{communicate}}$ is bounded by Paper 5's cheap talk framework.


# Temporal Learning {#sec:temporal-learning}

We formalize how an agent learns structure classes across sequential problem instances.

## Setup

Agent faces a sequence of problem instances $I_1, I_2, \ldots$ drawn from an unknown distribution $D$ over problem structures.

After solving instance $I_k$ (or abstaining), the agent observes:

-   Whether $I_k$ belonged to a tractable subcase

-   Which structure class $C_k$ was detected (if any)

-   The cost paid (substrate-dependent $\kappa$)

::: claim
Bayesian structure detectionth:bayesian-learning Agent maintains posterior $P(C \mid I_1, \ldots, I_k)$ over structure classes. Update rule: standard Bayesian update with likelihood $P(I_k \mid C)$. \[D:Tth:bayesian-learning; R:RG\]
:::

Convergence: does $P(C \mid I_1, \ldots, I_k) \to \delta_{C*}$ as $k \to \infty$?

Answer: yes, if the structure classes are identifiable (distinct likelihood functions).

::: claim
Identifiability implies convergenceprop:identifiability-convergence If structure classes $C$ are identifiable (distinct likelihood functions), then $P(C \mid I_1, \ldots, I_k) \to \delta_{C*}$ as $k \to \infty$. \[D:Pprop:identifiability-convergence; R:ID\]
:::

## PAC Learning Connection

Sample complexity of structure detection: How many instances must the agent solve before it can identify the structure class with probability $\geq 1 - \delta$ and error $\leq \varepsilon$?

::: claim
Sample complexity conjectureconj:sample-complexity For the represented family (bounded actions, separable utility, tree structure), sample complexity is polynomial in $1/\varepsilon$ and $\log(1/\delta)$. \[D:Jconj:sample-complexity; R:RG\]
:::

This connects to PAC learning theory---the structure classes are the hypothesis space.

## Learning Reduces Abstention

As the agent learns the structure class, it can apply regime-appropriate heuristics. The abstention frontier shrinks over time---not because the problem gets easier, but because the agent's model of the problem gets more accurate.

Formally: let $A_k$ be the set of instances where integrity forces abstention at time $k$. Then: $$A_1 \supseteq A_2 \supseteq \ldots \supseteq A_\infty$$ where $A_\infty =$ instances genuinely outside all tractable subcases.

::: claim
Abstention reduction over timeth:abstention-reduces $A_k$ is decreasing in $k$: $A_1 \supseteq A_2 \supseteq \ldots$. \[D:Tth:abstention-reduces; R:RG\]
:::

The agent's trajectory diverges based on $\kappa$ even though verdicts are $\kappa$-independent. Different substrates learn at different rates, have different abstention thresholds, and make different trade-offs between solving and abstaining.

This connects to Paper 5: temporal learning produces costly signals. Each solved instance is a costly signal in Paper 5's sense: producing a correct solution has truth-dependent cost. The agent's track record is costly signal; self-assessment is cheap talk.


# Temporal Integrity {#sec:temporal-integrity}

We formalize consistency of claims across sequences of problem instances.

## Definition

::: definition
[]{#def:temporal-integrity label="def:temporal-integrity"} Temporal integrity = consistency of claims across a sequence of instances.

An agent has temporal integrity if:

-   Each per-instance claim satisfies Paper 4's integrity constraint

-   Retractions are evidence-monotone: the agent retracts a claim only when new evidence contradicts it, never without cause

-   Refinements are monotone: if the agent claims $I$ is sufficient at time $t$, and later claims $I' \subset I$ is sufficient at time $t' > t$, this is a refinement (allowed). If it claims $I' \supset I$, this is a weakening that requires justification.
:::

::: decision
[]{#dec:temporal-integrity-check label="dec:temporal-integrity-check"} **TEMPORAL-INTEGRITY-CHECK**: Given a sequence of claims and evidence, is the sequence temporally integrity-preserving?
:::

::: claim
Retraction with evidence preserves integrityprop:retraction-evidence-integrity If an agent claimed $I$ sufficient, observed a counterexample, then retracted, this preserves temporal integrity. \[D:Pprop:retraction-evidence-integrity; R:RG\]
:::

::: claim
Retraction without evidence violates integrityprop:retraction-no-evidence-violates If an agent claimed $I$ sufficient, observed no new information, then retracted, this violates temporal integrity. \[D:Pprop:retraction-no-evidence-violates; R:RG\]
:::

::: claim
Refinement strengthens integrityprop:refinement-strengthens If an agent claimed $I$ sufficient, discovers $I' \subset I$ also sufficient, updates claim to $I'$. This preserves and strengthens temporal integrity. \[D:Pprop:refinement-strengthens; R:RG\]
:::

## Complexity of Temporal Integrity

::: claim
Complexity lower boundth:temporal-integrity-complexity TEMPORAL-INTEGRITY-CHECK is at least as hard as the base regime's SUFFICIENCY-CHECK. \[D:Tth:temporal-integrity-complexity; R:RG\]
:::

Each claim in the sequence requires verification. The temporal constraint (monotonicity) adds structure but doesn't reduce worst-case complexity.

Paper 4 proves integrity forces abstention. Paper 5 proves claiming integrity is cheap talk. Together: the agent must abstain (Paper 4), cannot credibly communicate why (Paper 5, cheap talk bound), and can only escape by producing costly signals (Paper 5, Theorem 4.1)---which are exactly the mechanized proofs that Paper 4 itself provides.


# Cross-Regime Transfer {#sec:cross-regime-transfer}

When does a sufficiency result in regime $R_1$ help in regime $R_2$?

## Transfer Conditions

1.  **Static $\to$ Stochastic**: Transfers iff distribution $P$ concentrates on a tractable static subcase. Formally: if $\text{supp}(P)$ lies within a structure-detectable class $C$, then static sufficiency for $C$ implies stochastic sufficiency under $P$. Otherwise: bridge failure (already mechanized).

2.  **Static $\to$ Sequential**: Transfers iff horizon $T = 1$ and transitions are deterministic. This is the one-step bridge (already proved in Paper 4: ). For $T > 1$: bridge failure ().

3.  **Stochastic $\to$ Sequential**: Transfers iff transitions are memoryless AND observation model is regime-compatible. Formally: if $T(s'|a,s)$ depends only on the stochastically sufficient coordinates of $s$, then stochastic sufficiency lifts to sequential sufficiency. Otherwise: new bridge-failure witness needed.

4.  **Sequential $\to$ Static**: Always degenerates. A sequential problem with $T=1$ and deterministic transitions IS a static problem.

::: claim
Transfer static to stochasticth:transfer-static-stochastic Static sufficiency transfers to stochastic iff $P$ concentrates on tractable subcase. \[D:Tth:transfer-static-stochastic; R:RG\]
:::

::: claim
Transfer stochastic to sequentialth:transfer-stochastic-sequential Stochastic sufficiency transfers to sequential iff memoryless transitions and regime-compatible observations. \[D:Tth:transfer-stochastic-sequential; R:RG\]
:::

## Heuristic Transfer Across Regimes

Paper 4's heuristic reusability bridge generalizes: if structure detection is polynomial in regime $R_1$, and the detected structure is preserved under regime extension to $R_2$, then the heuristic transfers.

Key question: when is structure preserved?

-   Product distributions preserve separable utility

-   Deterministic transitions preserve tree structure


# Related Work {#sec:related}

This paper extends the static decision quotient to stochastic and sequential regimes. Related work falls into several categories.

## Complexity of Dynamic Decision Problems

The complexity of MDPs and POMDPs is well-established: optimal MDP planning is in P, optimal POMDP planning is PSPACE-complete [@papadimitriou1987mdp; @mundhenk2000mdp; @littman1998probplanning]. Our contribution extends this to the meta-question of identifying sufficient coordinates in these settings.

Sufficient statistics [@fisher1922mathematical] is the classical foundation. Our stochastic sufficiency definition connects to this tradition but focuses on decision-relevant information rather than statistical estimation.

## Information and Signaling

Value of information [@howard1966information; @raiffa1961applied] quantifies payment for information. We address a different question: the complexity of identifying which information is sufficient for decision.

Signaling games [@spence1973job; @myerson1979incentive; @milgrom1986price] connect to our temporal integrity and credibility results (Paper 5). The agent must abstain (Paper 4), cannot credibly signal why (Paper 5), and can only escape via costly signals.

## Feature Selection in Machine Learning

Feature selection asks which inputs predict outputs, known NP-hard in general [@blum1997selection; @amaldi1998complexity; @guyon2003introduction]. Our decision-theoretic analog for sufficiency is PP-complete (stochastic) and PSPACE-complete (sequential).

## Regime Complexity Hierarchy

Our hierarchy Static $\subset$ Stochastic $\subset$ Sequential with complexity classes coNP $\subset$ PP $\subset$ PSPACE extends the representation-sensitive complexity results established for MDPs/POMDPs to the meta-level sufficiency problem.

This paper integrates: (i) stochastic and sequential extensions, (ii) substrate cost formalization, (iii) temporal learning and integrity, and (iv) cross-regime transfer conditions.


# Conclusion {#sec:conclusion}

This paper extends the static decision quotient to stochastic and sequential regimes.

## Summary of Results {#summary-of-results .unnumbered}

-   **Stochastic sufficiency** (Section [\[sec:stochastic\]](#sec:stochastic){reference-type="ref" reference="sec:stochastic"}): STOCHASTIC-SUFFICIENCY-CHECK is PP-complete via MAJSAT reduction. Tractable under product distributions, bounded support, log-concave.

-   **Sequential sufficiency** (Section [\[sec:sequential\]](#sec:sequential){reference-type="ref" reference="sec:sequential"}): SEQUENTIAL-SUFFICIENCY-CHECK is PSPACE-complete via TQBF reduction. Tractable under full observability, bounded horizon, tree structure.

-   **Regime hierarchy** (Section [\[sec:regime-hierarchy\]](#sec:regime-hierarchy){reference-type="ref" reference="sec:regime-hierarchy"}): Static $\subset$ Stochastic $\subset$ Sequential; coNP $\subset$ PP $\subset$ PSPACE.

-   **Substrate cost** (Section [\[sec:substrate-cost\]](#sec:substrate-cost){reference-type="ref" reference="sec:substrate-cost"}): Verdict is $\kappa$-independent; trajectory is $\kappa$-dependent.

-   **Temporal learning** (Section [\[sec:temporal-learning\]](#sec:temporal-learning){reference-type="ref" reference="sec:temporal-learning"}): Bayesian structure detection reduces abstention over time.

-   **Temporal integrity** (Section [\[sec:temporal-integrity\]](#sec:temporal-integrity){reference-type="ref" reference="sec:temporal-integrity"}): Evidence-monotone retractions preserve integrity.

These results place stochastic and sequential sufficiency at higher complexity levels than static sufficiency.

## Open Questions {#open-questions .unnumbered}

-   **Exact transfer conditions:** Characterize when stochastic sufficiency transfers to sequential.

-   **PAC learning bounds:** Prove sample complexity bounds for structure detection.

-   **Temporal integrity complexity:** Tight complexity bounds for TEMPORAL-INTEGRITY-CHECK.

This work extends Paper 4's framework to dynamic settings while preserving the core insight: identifying sufficient information is computationally hard, and integrity forces abstention when resources don't match problem complexity.


# Lean 4 Proof Listings {#app:lean}

The complete Lean 4 formalization extends the Paper 4 artifact. The mechanization consists of 3288 lines across 29 files, with 124 theorem/lemma statements.

**Handle IDs.** Inline theorem metadata cites compact IDs (for example, `CC4`, `HD2`, `IC3`) instead of full theorem constants.

## Lean Handle ID Map {#sec:lean-handle-id-map-4b}

## What Is Machine-Checked

The Lean formalization establishes:

1.  **STOCHASTIC-SUFFICIENCY PP-completeness**: Reduction from MAJSAT showing stochastic sufficiency checking is PP-complete.

2.  **SEQUENTIAL-SUFFICIENCY PSPACE-completeness**: Reduction from TQBF showing sequential sufficiency checking is PSPACE-complete.

3.  **Substrate independence theorems**: Formal proofs that the matrix verdict is $\kappa$-independent while trajectories are $\kappa$-dependent.

4.  **Bridge transfer conditions**: Formalized conditions under which sufficiency transfers between regimes.

## Complete Claim Coverage Matrix

## Claims Not Fully Mechanized

Entries marked **Full (conditional)** are explicitly mechanized transfer theorems that depend on standard external complexity facts (e.g., MAJSAT PP-completeness, TQBF PSPACE-completeness), with those dependencies represented as hypotheses in Lean.

## Verification

The proofs compile with Lean 4. Run `lake build` in the proof directory to verify.


+------------------------+--------------------------------------------------------------------------------------------------------+
| ID                     | Full Lean handle                                                                                       |
+:=======================+:=======================================================================================================+
| ID                     | Full Lean handle (continued)                                                                           |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR1}          | `AccessRegime.le`                                                                                      |
| [AR1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR2}          | `AccessRegime.answer_space`                                                                            |
| [AR2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR3}          | `AccessRegime.le_refl`                                                                                 |
| [AR3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR4}          | `AccessRegime.le_trans`                                                                                |
| [AR4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR5}          | `AccessRegime.query_space`                                                                             |
| [AR5]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AU1}          | `AdditiveUtility.isRelevant`                                                                           |
| [AU1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AU2}          | `AdditiveUtility.relevantSet`                                                                          |
| [AU2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AU3}          | `AdditiveUtility.toProblem`                                                                            |
| [AU3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:BC1}          | `BooleanCircuit.circuitSize`                                                                           |
| [BC1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C1}           | `Complexity.BitStr`                                                                                    |
| [C1]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C2}           | `Complexity.Decides`                                                                                   |
| [C2]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C3}           | `Complexity.KarpReduces`                                                                               |
| [C3]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C4}           | `Complexity.Lang`                                                                                      |
| [C4]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C5}           | `Complexity.ManyOneReducesPoly`                                                                        |
| [C5]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C6}           | `Complexity.P`                                                                                         |
| [C6]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C7}           | `Complexity.PolyTime`                                                                                  |
| [C7]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C8}           | `Complexity.bitEnc`                                                                                    |
| [C8]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C9}           | `Counted.bind`                                                                                         |
| [C9]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C10}          | `Counted.bind_steps`                                                                                   |
| [C10]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C11}          | `Counted.pure`                                                                                         |
| [C11]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C12}          | `Counted.pure_steps`                                                                                   |
| [C12]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C13}          | `Counted.result`                                                                                       |
| [C13]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C14}          | `Counted.steps`                                                                                        |
| [C14]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C15}          | `Counted.steps_eq_fst`                                                                                 |
| [C15]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C16}          | `Counted.tick`                                                                                         |
| [C16]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C17}          | `Counted.tick_bind_steps`                                                                              |
| [C17]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C31}          | `Clause3.eval`                                                                                         |
| [C31]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC1}          | `DecisionQuotient.ClaimClosure.RegimeSimulation`                                                       |
| [CC1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC2}          | `DecisionQuotient.ClaimClosure.adq_ordering`                                                           |
| [CC2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC3}          | `DecisionQuotient.ClaimClosure.agent_transfer_licensed_iff_snapshot`                                   |
| [CC3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC4}          | `DecisionQuotient.ClaimClosure.anchor_sigma2p_complete_conditional`                                    |
| [CC4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC5}          | `DecisionQuotient.ClaimClosure.anchor_sigma2p_reduction_core`                                          |
| [CC5]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC6}          | `DecisionQuotient.ClaimClosure.boundaryCharacterized_iff_exists_sufficient_subset`                     |
| [CC6]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC7}          | `DecisionQuotient.ClaimClosure.bounded_actions_detectable`                                             |
| [CC7]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC8}          | `DecisionQuotient.ClaimClosure.bridge_boundary_represented_family`                                     |
| [CC8]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC9}          | `DecisionQuotient.ClaimClosure.bridge_failure_witness_non_one_step`                                    |
| [CC9]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC10}         | `DecisionQuotient.ClaimClosure.bridge_transfer_iff_one_step_class`                                     |
| [CC10]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC11}         | `DecisionQuotient.ClaimClosure.certified_total_bits_split_core`                                        |
| [CC11]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC12}         | `DecisionQuotient.ClaimClosure.cost_asymmetry_eth_conditional`                                         |
| [CC12]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC13}         | `DecisionQuotient.ClaimClosure.declaredBudgetSlice`                                                    |
| [CC13]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC14}         | `DecisionQuotient.ClaimClosure.declaredRegimeFamily_complete`                                          |
| [CC14]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC15}         | `DecisionQuotient.ClaimClosure.declared_physics_no_universal_exact_certifier_core`                     |
| [CC15]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC16}         | `DecisionQuotient.ClaimClosure.dichotomy_conditional`                                                  |
| [CC16]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC17}         | `DecisionQuotient.ClaimClosure.epsilon_admissible_iff_raw_lt_certified_total_core`                     |
| [CC17]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC18}         | `DecisionQuotient.ClaimClosure.exact_admissible_iff_raw_lt_certified_total_core`                       |
| [CC18]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC19}         | `DecisionQuotient.ClaimClosure.exact_certainty_inflation_under_hardness_core`                          |
| [CC19]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC20}         | `DecisionQuotient.ClaimClosure.exact_raw_eq_certified_iff_certainty_inflation_core`                    |
| [CC20]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC21}         | `DecisionQuotient.ClaimClosure.exact_raw_only_of_no_exact_admissible_core`                             |
| [CC21]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC22}         | `DecisionQuotient.ClaimClosure.explicit_assumptions_required_of_not_excused_core`                      |
| [CC22]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC23}         | `DecisionQuotient.ClaimClosure.explicit_state_upper_core`                                              |
| [CC23]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC24}         | `DecisionQuotient.ClaimClosure.hard_family_all_coords_core`                                            |
| [CC24]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC25}         | `DecisionQuotient.ClaimClosure.horizonTwoWitness_immediate_empty_sufficient`                           |
| [CC25]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC26}         | `DecisionQuotient.ClaimClosure.horizon_gt_one_bridge_can_fail_on_sufficiency`                          |
| [CC26]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC27}         | `DecisionQuotient.ClaimClosure.information_barrier_opt_oracle_core`                                    |
| [CC27]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC28}         | `DecisionQuotient.ClaimClosure.information_barrier_state_batch_core`                                   |
| [CC28]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC29}         | `DecisionQuotient.ClaimClosure.information_barrier_value_entry_core`                                   |
| [CC29]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC30}         | `DecisionQuotient.ClaimClosure.integrity_resource_bound_for_sufficiency`                               |
| [CC30]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC31}         | `DecisionQuotient.ClaimClosure.integrity_universal_applicability_core`                                 |
| [CC31]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC32}         | `DecisionQuotient.ClaimClosure.meta_coordinate_irrelevant_of_invariance_on_declared_slice`             |
| [CC32]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC33}         | `DecisionQuotient.ClaimClosure.meta_coordinate_not_relevant_on_declared_slice`                         |
| [CC33]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC34}         | `ComplexityClass.lt`                                                                                   |
| [CC34]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC35}         | `DecisionQuotient.ClaimClosure.minsuff_collapse_to_conp_conditional`                                   |
| [CC35]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC36}         | `DecisionQuotient.ClaimClosure.minsuff_conp_complete_conditional`                                      |
| [CC36]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC37}         | `DecisionQuotient.ClaimClosure.no_auto_minimize_of_p_neq_conp`                                         |
| [CC37]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC38}         | `DecisionQuotient.ClaimClosure.no_exact_claim_admissible_under_hardness_core`                          |
| [CC38]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC39}         | `DecisionQuotient.ClaimClosure.no_exact_claim_under_declared_assumptions_unless_excused_core`          |
| [CC39]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC40}         | `DecisionQuotient.ClaimClosure.no_exact_identifier_implies_not_boundary_characterized`                 |
| [CC40]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC41}         | `DecisionQuotient.ClaimClosure.no_uncertified_exact_claim_core`                                        |
| [CC41]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC42}         | `DecisionQuotient.ClaimClosure.one_step_bridge`                                                        |
| [CC42]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC43}         | `DecisionQuotient.ClaimClosure.oracle_lattice_transfer_as_regime_simulation`                           |
| [CC43]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC44}         | `DecisionQuotient.ClaimClosure.physical_crossover_above_cap_core`                                      |
| [CC44]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC45}         | `DecisionQuotient.ClaimClosure.physical_crossover_core`                                                |
| [CC45]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC46}         | `DecisionQuotient.ClaimClosure.physical_crossover_hardness_core`                                       |
| [CC46]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC47}         | `DecisionQuotient.ClaimClosure.physical_crossover_policy_core`                                         |
| [CC47]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC48}         | `DecisionQuotient.ClaimClosure.process_bridge_failure_witness`                                         |
| [CC48]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC49}         | `DecisionQuotient.ClaimClosure.query_obstruction_boolean_corollary`                                    |
| [CC49]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC50}         | `DecisionQuotient.ClaimClosure.query_obstruction_finite_state_core`                                    |
| [CC50]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC51}         | `DecisionQuotient.ClaimClosure.regime_core_claim_proved`                                               |
| [CC51]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC52}         | `DecisionQuotient.ClaimClosure.regime_simulation_transfers_hardness`                                   |
| [CC52]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC53}         | `DecisionQuotient.ClaimClosure.reusable_heuristic_of_detectable`                                       |
| [CC53]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC54}         | `DecisionQuotient.ClaimClosure.selectorSufficient_not_implies_setSufficient`                           |
| [CC54]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC55}         | `DecisionQuotient.ClaimClosure.separable_detectable`                                                   |
| [CC55]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC56}         | `DecisionQuotient.ClaimClosure.snapshot_vs_process_typed_boundary`                                     |
| [CC56]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC57}         | `DecisionQuotient.ClaimClosure.standard_assumption_ledger_unpack`                                      |
| [CC57]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC58}         | `DecisionQuotient.ClaimClosure.stochastic_objective_bridge_can_fail_on_sufficiency`                    |
| [CC58]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC59}         | `DecisionQuotient.ClaimClosure.subproblem_hardness_lifts_to_full`                                      |
| [CC59]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC60}         | `DecisionQuotient.ClaimClosure.subproblem_transfer_as_regime_simulation`                               |
| [CC60]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC61}         | `DecisionQuotient.ClaimClosure.sufficiency_conp_complete_conditional`                                  |
| [CC61]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC62}         | `DecisionQuotient.ClaimClosure.sufficiency_conp_reduction_core`                                        |
| [CC62]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC63}         | `DecisionQuotient.ClaimClosure.sufficiency_iff_dq_ratio`                                               |
| [CC63]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC64}         | `DecisionQuotient.ClaimClosure.sufficiency_iff_projectedOptCover_eq_opt`                               |
| [CC64]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC65}         | `DecisionQuotient.ClaimClosure.thermo_conservation_additive_core`                                      |
| [CC65]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC66}         | `DecisionQuotient.ClaimClosure.thermo_energy_carbon_lift_core`                                         |
| [CC66]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC67}         | `DecisionQuotient.ClaimClosure.thermo_eventual_lift_core`                                              |
| [CC67]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC68}         | `DecisionQuotient.ClaimClosure.thermo_hardness_bundle_core`                                            |
| [CC68]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC69}         | `DecisionQuotient.ClaimClosure.thermo_mandatory_cost_core`                                             |
| [CC69]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC70}         | `DecisionQuotient.ClaimClosure.tractable_bounded_core`                                                 |
| [CC70]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC71}         | `DecisionQuotient.ClaimClosure.tractable_separable_core`                                               |
| [CC71]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC72}         | `DecisionQuotient.ClaimClosure.tractable_subcases_conditional`                                         |
| [CC72]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC73}         | `DecisionQuotient.ClaimClosure.tractable_tree_core`                                                    |
| [CC73]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC74}         | `DecisionQuotient.ClaimClosure.transition_coupled_bridge_can_fail_on_sufficiency`                      |
| [CC74]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC75}         | `DecisionQuotient.ClaimClosure.tree_structure_detectable`                                              |
| [CC75]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC76}         | `DecisionQuotient.ClaimClosure.typed_claim_admissibility_core`                                         |
| [CC76]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC77}         | `DecisionQuotient.ClaimClosure.typed_static_class_completeness`                                        |
| [CC77]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC78}         | `DecisionQuotient.ClaimClosure.universal_solver_framing_core`                                          |
| [CC78]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP1}         | `ComputableDecisionProblem.checkSufficiency`                                                           |
| [CDP1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP2}         | `ComputableDecisionProblem.checkSufficiency_iff_abstract`                                              |
| [CDP2]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP3}         | `ComputableDecisionProblem.computeOpt`                                                                 |
| [CDP3]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP4}         | `ComputableDecisionProblem.computeOpt_eq_abstract`                                                     |
| [CDP4]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP5}         | `ComputableDecisionProblem.decisionEquivDec`                                                           |
| [CDP5]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP6}         | `ComputableDecisionProblem.decisionEquivDec_iff`                                                       |
| [CDP6]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP7}         | `ComputableDecisionProblem.decisionEquivDec_iff_abstract`                                              |
| [CDP7]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP8}         | `ComputableDecisionProblem.insufficiencyWitnesses`                                                     |
| [CDP8]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP9}         | `ComputableDecisionProblem.isOptimalDec`                                                               |
| [CDP9]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP10}        | `ComputableDecisionProblem.isOptimalDec_iff`                                                           |
| [CDP10]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP11}        | `ComputableDecisionProblem.isOptimalDec_iff_abstract`                                                  |
| [CDP11]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP12}        | `ComputableDecisionProblem.mem_computeOpt_iff`                                                         |
| [CDP12]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP13}        | `ComputableDecisionProblem.toAbstract`                                                                 |
| [CDP13]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP14}        | `ComputableDecisionProblem.verifyWitness`                                                              |
| [CDP14]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CR1}          | `DecisionQuotient.ConfigReduction.config_sufficiency_iff_behavior_preserving`                          |
| [CR1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP1}          | `DecisionQuotient.DecisionProblem.minimalSufficient_iff_relevant`                                      |
| [DP1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP2}          | `DecisionQuotient.DecisionProblem.relevantSet_is_minimal`                                              |
| [DP2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP3}          | `DecisionQuotient.DecisionProblem.sufficient_implies_selectorSufficient`                               |
| [DP3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP4}          | `DecisionQuotient.ClaimClosure.DecisionProblem.epsOpt_zero_eq_opt`                                     |
| [DP4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP5}          | `DecisionQuotient.ClaimClosure.DecisionProblem.sufficient_iff_zeroEpsilonSufficient`                   |
| [DP5]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP6}          | `DecisionProblem.anchorSufficient`                                                                     |
| [DP6]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP7}          | `DecisionProblem.classMonotoneOn`                                                                      |
| [DP7]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP8}          | `DecisionProblem.constant_opt_all_sufficient`                                                          |
| [DP8]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP9}          | `DecisionProblem.DecisionEquiv`                                                                        |
| [DP9]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP10}         | `DecisionProblem.DecisionQuotientType`                                                                 |
| [DP10]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP11}         | `DecisionProblem.Opt`                                                                                  |
| [DP11]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP12}         | `DecisionProblem.OptQuotient`                                                                          |
| [DP12]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP13}         | `DecisionProblem.SelectedAction`                                                                       |
| [DP13]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP14}         | `DecisionProblem.decisionEquiv_refl`                                                                   |
| [DP14]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP15}         | `DecisionProblem.decisionEquiv_symm`                                                                   |
| [DP15]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP16}         | `DecisionProblem.decisionEquiv_trans`                                                                  |
| [DP16]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP17}         | `DecisionProblem.decisionSetoid`                                                                       |
| [DP17]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP18}         | `DecisionProblem.dominant_all_sufficient`                                                              |
| [DP18]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP19}         | `DecisionProblem.dominant_unique`                                                                      |
| [DP19]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP20}         | `DecisionProblem.edgeOnComplement`                                                                     |
| [DP20]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP21}         | `DecisionProblem.edgeOnComplement_iff_not_sufficient`                                                  |
| [DP21]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP22}         | `DecisionProblem.emptySet_not_sufficient_iff_exists_opt_difference`                                    |
| [DP22]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP23}         | `DecisionProblem.emptySet_sufficient_iff_constant`                                                     |
| [DP23]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP24}         | `DecisionProblem.epsOpt`                                                                               |
| [DP24]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP25}         | `DecisionProblem.epsOpt_zero_eq_opt`                                                                   |
| [DP25]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP26}         | `DecisionProblem.erase_of_not_mem`                                                                     |
| [DP26]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP27}         | `DecisionProblem.factors_implies_respects`                                                             |
| [DP27]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP28}         | `DecisionProblem.hasConstantOpt`                                                                       |
| [DP28]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP29}         | `DecisionProblem.hasConstantOpt'`                                                                      |
| [DP29]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP30}         | `DecisionProblem.hasDominant`                                                                          |
| [DP30]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP31}         | `DecisionProblem.irrelevant_iff_not_relevant`                                                          |
| [DP31]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP32}         | `DecisionProblem.isEpsilonSufficient`                                                                  |
| [DP32]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP33}         | `DecisionProblem.isIrrelevant`                                                                         |
| [DP33]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP34}         | `DecisionProblem.isMinimalSufficient`                                                                  |
| [DP34]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP35}         | `DecisionProblem.isMinimalSufficient'`                                                                 |
| [DP35]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP36}         | `DecisionProblem.isOptimal`                                                                            |
| [DP36]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP37}         | `DecisionProblem.isRelevant`                                                                           |
| [DP37]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP38}         | `DecisionProblem.isSelectorSufficient`                                                                 |
| [DP38]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP39}         | `DecisionProblem.isSufficient`                                                                         |
| [DP39]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP40}         | `DecisionProblem.isSufficientAt`                                                                       |
| [DP40]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP41}         | `DecisionProblem.isSufficientOnSet`                                                                    |
| [DP41]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP42}         | `DecisionProblem.minimalSufficient_all_relevant'`                                                      |
| [DP42]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP43}         | `DecisionProblem.minimalSufficient_eq_relevant'`                                                       |
| [DP43]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP44}         | `DecisionProblem.minimalSufficient_iff_relevant`                                                       |
| [DP44]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP45}         | `DecisionProblem.monotoneIn`                                                                           |
| [DP45]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP46}         | `DecisionProblem.nonnegativelyMonotoneCoord`                                                           |
| [DP46]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP47}         | `DecisionProblem.not_sufficient_iff_exists_counterexample`                                             |
| [DP47]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP48}         | `DecisionProblem.numOptClasses`                                                                        |
| [DP48]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP49}         | `DecisionProblem.numOptClasses_le`                                                                     |
| [DP49]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP50}         | `DecisionProblem.numOptClasses_pos`                                                                    |
| [DP50]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP51}         | `DecisionProblem.opt_eq_optQuotient_comp`                                                              |
| [DP51]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP52}         | `DecisionProblem.opt_factors_through_quotient`                                                         |
| [DP52]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP53}         | `DecisionProblem.preservesOpt`                                                                         |
| [DP53]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP54}         | `DecisionProblem.preservesOptStrong`                                                                   |
| [DP54]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP55}         | `DecisionProblem.quotientEntropy`                                                                      |
| [DP55]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP56}         | `DecisionProblem.quotientEntropy_nonneg`                                                               |
| [DP56]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP57}         | `DecisionProblem.quotientEntropy_zero_of_constant`                                                     |
| [DP57]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP58}         | `DecisionProblem.quotientMap`                                                                          |
| [DP58]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP59}         | `DecisionProblem.quotientMap_preservesOpt`                                                             |
| [DP59]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP60}         | `DecisionProblem.quotientSize`                                                                         |
| [DP60]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP61}         | `DecisionProblem.quotient_is_coarsest`                                                                 |
| [DP61]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP62}         | `DecisionProblem.quotient_represents_opt_equiv`                                                        |
| [DP62]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP63}         | `DecisionProblem.relevantSet`                                                                          |
| [DP63]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP64}         | `DecisionProblem.relevantSet_is_minimal`                                                               |
| [DP64]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP65}         | `DecisionProblem.relevant_necessary`                                                                   |
| [DP65]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP66}         | `DecisionProblem.sufficientSets`                                                                       |
| [DP66]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP67}         | `DecisionProblem.sufficientSets_principal'`                                                            |
| [DP67]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP68}         | `DecisionProblem.sufficientSets_upward`                                                                |
| [DP68]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP69}         | `DecisionProblem.sufficientSets_upward_closed`                                                         |
| [DP69]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP70}         | `DecisionProblem.sufficient_contains_all_relevant`                                                     |
| [DP70]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP71}         | `DecisionProblem.sufficient_contains_relevant`                                                         |
| [DP71]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP72}         | `DecisionProblem.sufficient_erase_irrelevant'`                                                         |
| [DP72]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP73}         | `DecisionProblem.sufficient_iff_zeroEpsilonSufficient`                                                 |
| [DP73]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP74}         | `DecisionProblem.sufficient_implies_selectorSufficient`                                                |
| [DP74]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP75}         | `DecisionProblem.sufficient_superset`                                                                  |
| [DP75]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP76}         | `DecisionProblem.univ_sufficient_of_injective`                                                         |
| [DP76]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ1}          | `DecisionQuotient.AdditiveUtility`                                                                     |
| [DQ1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ2}          | `DecisionQuotient.AssignX`                                                                             |
| [DQ2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ3}          | `DecisionQuotient.AssignY`                                                                             |
| [DQ3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ4}          | `DecisionQuotient.Assignment`                                                                          |
| [DQ4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ5}          | `DecisionQuotient.BinaryState`                                                                         |
| [DQ5]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ6}          | `DecisionQuotient.BooleanCircuit`                                                                      |
| [DQ6]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ7}          | `DecisionQuotient.CircuitDecisionProblem`                                                              |
| [DQ7]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ8}          | `DecisionQuotient.ClaimClosure.agreeOn_refl`                                                           |
| [DQ8]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ9}          | `DecisionQuotient.ClaimClosure.agreeOn_symm`                                                           |
| [DQ9]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ10}         | `DecisionQuotient.ClaimClosure.agreeOn_trans`                                                          |
| [DQ10]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ11}         | `DecisionQuotient.ClaimClosure.irrelevantOn_implies_not_relevantOn`                                    |
| [DQ11]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ12}         | `DecisionQuotient.ClaimClosure.isIrrelevantOn`                                                         |
| [DQ12]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ13}         | `DecisionQuotient.ClaimClosure.isRelevantOn`                                                           |
| [DQ13]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ14}         | `DecisionQuotient.Clause3`                                                                             |
| [DQ14]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ15}         | `DecisionQuotient.ComputableDecisionProblem`                                                           |
| [DQ15]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ16}         | `DecisionQuotient.ConfigReduction.ConfigAction`                                                        |
| [DQ16]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ17}         | `DecisionQuotient.ConfigReduction.behaviorPreserving`                                                  |
| [DQ17]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ18}         | `DecisionQuotient.ConfigReduction.configDecisionProblem`                                               |
| [DQ18]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ19}         | `DecisionQuotient.ConfigReduction.configUtility`                                                       |
| [DQ19]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ20}         | `DecisionQuotient.ConfigReduction.configUtility_le_one`                                                |
| [DQ20]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ21}         | `DecisionQuotient.ConfigReduction.no_occurs_iff_of_behaviorPreserving`                                 |
| [DQ21]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ22}         | `DecisionQuotient.ConfigReduction.none_mem_Opt_iff_no_occurs`                                          |
| [DQ22]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ23}         | `DecisionQuotient.ConfigReduction.some_mem_Opt_iff_occurs`                                             |
| [DQ23]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ24}         | `DecisionQuotient.ConfigReduction.some_mem_Opt_of_occurs`                                              |
| [DQ24]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ25}         | `DecisionQuotient.ConfigReduction.some_not_mem_Opt_of_not_occurs`                                      |
| [DQ25]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ26}         | `DecisionQuotient.CoordinateSpace`                                                                     |
| [DQ26]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ27}         | `DecisionQuotient.Counted`                                                                             |
| [DQ27]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ28}         | `DecisionQuotient.DQAction`                                                                            |
| [DQ28]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ29}         | `DecisionQuotient.DQInstance`                                                                          |
| [DQ29]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ30}         | `DecisionQuotient.DecisionProblem`                                                                     |
| [DQ30]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ31}         | `DecisionQuotient.EncodedDecisionProblem`                                                              |
| [DQ31]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ32}         | `DecisionQuotient.ExistsForallFormula`                                                                 |
| [DQ32]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ33}         | `DecisionQuotient.ExistsForallFormula.embedVar`                                                        |
| [DQ33]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ34}         | `DecisionQuotient.ExistsForallFormula.eval_padUniversal`                                               |
| [DQ34]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ35}         | `DecisionQuotient.ExistsForallFormula.padUniversal`                                                    |
| [DQ35]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ36}         | `DecisionQuotient.ExistsForallFormula.restrictY`                                                       |
| [DQ36]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ37}         | `DecisionQuotient.ExistsForallFormula.satisfiable`                                                     |
| [DQ37]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ38}         | `DecisionQuotient.ExistsForallFormula.satisfiable_iff_padUniversal`                                    |
| [DQ38]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ39}         | `DecisionQuotient.ExistsForallFormula.satisfiedBy`                                                     |
| [DQ39]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ40}         | `DecisionQuotient.ExistsForallFormula.sumAssignment`                                                   |
| [DQ40]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ41}         | `DecisionQuotient.ExistsForallFormula.sumAssignment_embed`                                             |
| [DQ41]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ42}         | `DecisionQuotient.FiniteDecisionProblem`                                                               |
| [DQ42]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ43}         | `DecisionQuotient.FiniteDecisionProblem.decisionQuotient`                                              |
| [DQ43]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ44}         | `DecisionQuotient.FiniteDecisionProblem.isSufficient`                                                  |
| [DQ44]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ45}         | `DecisionQuotient.FiniteDecisionProblem.isSufficient_superset`                                         |
| [DQ45]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ46}         | `DecisionQuotient.FiniteDecisionProblem.mem_optimalActions_iff`                                        |
| [DQ46]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ47}         | `DecisionQuotient.FiniteDecisionProblem.optimalActions`                                                |
| [DQ47]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ48}         | `DecisionQuotient.FiniteDecisionProblem.optimalActions_subset_actions`                                 |
| [DQ48]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ49}         | `DecisionQuotient.FiniteDecisionProblem.toDecisionProblem`                                             |
| [DQ49]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ50}         | `DecisionQuotient.HardnessDistribution.IsEventuallyConstant`                                           |
| [DQ50]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ51}         | `DecisionQuotient.HardnessDistribution.SolutionArchitecture`                                           |
| [DQ51]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ52}         | `DecisionQuotient.HardnessDistribution.SpecificationProblem`                                           |
| [DQ52]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ53}         | `DecisionQuotient.HardnessDistribution.amortizationThreshold`                                          |
| [DQ53]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ54}         | `DecisionQuotient.HardnessDistribution.amortization_threshold_native_manual`                           |
| [DQ54]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ55}         | `DecisionQuotient.HardnessDistribution.centralization_step_reduces_total`                              |
| [DQ55]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ56}         | `DecisionQuotient.HardnessDistribution.centralized_constant`                                           |
| [DQ56]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ57}         | `DecisionQuotient.HardnessDistribution.centralized_minimal_errors`                                     |
| [DQ57]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ58}         | `DecisionQuotient.HardnessDistribution.distributed_errors_grow`                                        |
| [DQ58]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ59}         | `DecisionQuotient.HardnessDistribution.distributed_multiplies`                                         |
| [DQ59]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ60}         | `DecisionQuotient.HardnessDistribution.dof_conservation`                                               |
| [DQ60]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ61}         | `DecisionQuotient.HardnessDistribution.errorSites`                                                     |
| [DQ61]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ62}         | `DecisionQuotient.HardnessDistribution.gapCard`                                                        |
| [DQ62]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ63}         | `DecisionQuotient.HardnessDistribution.generalizedTotalDOF`                                            |
| [DQ63]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ64}         | `DecisionQuotient.HardnessDistribution.generalized_right_dominates_wrong_pointwise`                    |
| [DQ64]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ65}         | `DecisionQuotient.HardnessDistribution.hardnessEfficiency`                                             |
| [DQ65]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ66}         | `DecisionQuotient.HardnessDistribution.less_distributed_less_total`                                    |
| [DQ66]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ67}         | `DecisionQuotient.HardnessDistribution.leverageRatio`                                                  |
| [DQ67]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ68}         | `DecisionQuotient.HardnessDistribution.linear_lt_exponential_eventually`                               |
| [DQ68]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ69}         | `DecisionQuotient.HardnessDistribution.linear_represents_saturating_only_zero_slope`                   |
| [DQ69]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ70}         | `DecisionQuotient.HardnessDistribution.manualApproach`                                                 |
| [DQ70]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ71}         | `DecisionQuotient.HardnessDistribution.manual_errors_grow`                                             |
| [DQ71]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ72}         | `DecisionQuotient.HardnessDistribution.manual_is_wrong`                                                |
| [DQ72]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ73}         | `DecisionQuotient.HardnessDistribution.nativeTypeSystem`                                               |
| [DQ73]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ74}         | `DecisionQuotient.HardnessDistribution.native_is_right`                                                |
| [DQ74]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ75}         | `DecisionQuotient.HardnessDistribution.native_minimal_errors`                                          |
| [DQ75]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ76}         | `DecisionQuotient.HardnessDistribution.right_fewer_error_sites`                                        |
| [DQ76]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ77}         | `DecisionQuotient.HardnessDistribution.saturatingSiteCost`                                             |
| [DQ77]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ78}         | `DecisionQuotient.HardnessDistribution.simplicityTax`                                                  |
| [DQ78]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ79}         | `DecisionQuotient.HardnessDistribution.simplicityTax_conservation`                                     |
| [DQ79]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ80}         | `DecisionQuotient.HardnessDistribution.totalDOF`                                                       |
| [DQ80]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ81}         | `DecisionQuotient.HardnessDistribution.totalDOF_eventually_constant_of_zero_distributed`               |
| [DQ81]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ82}         | `DecisionQuotient.HardnessDistribution.totalExternalWork`                                              |
| [DQ82]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ83}         | `DecisionQuotient.HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`                             |
| [DQ83]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ84}         | `DecisionQuotient.HardnessDistribution.zero_distributed_of_totalDOF_eventually_constant`               |
| [DQ84]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ85}         | `DecisionQuotient.InP`                                                                                 |
| [DQ85]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ86}         | `DecisionQuotient.InsufficiencyWitness`                                                                |
| [DQ86]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ87}         | `DecisionQuotient.IntegrityCompetence.CertifyingSolver`                                                |
| [DQ87]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ88}         | `DecisionQuotient.IntegrityCompetence.ClaimAdmissible`                                                 |
| [DQ88]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ89}         | `DecisionQuotient.IntegrityCompetence.CompetentOn`                                                     |
| [DQ89]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ90}         | `DecisionQuotient.IntegrityCompetence.EpsilonCompetentOn`                                              |
| [DQ90]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ91}         | `DecisionQuotient.IntegrityCompetence.EpsilonRelation`                                                 |
| [DQ91]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ92}         | `DecisionQuotient.IntegrityCompetence.Regime`                                                          |
| [DQ92]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ93}         | `DecisionQuotient.IntegrityCompetence.SolverIntegrity`                                                 |
| [DQ93]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ94}         | `DecisionQuotient.IntegrityCompetence.admissibleIrrationalCount`                                       |
| [DQ94]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ95}         | `DecisionQuotient.IntegrityCompetence.admissibleRationalCount`                                         |
| [DQ95]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ96}         | `DecisionQuotient.IntegrityCompetence.admissible_epsilon_implies_integrity`                            |
| [DQ96]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ97}         | `DecisionQuotient.IntegrityCompetence.admissible_exact_implies_integrity`                              |
| [DQ97]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ98}         | `DecisionQuotient.IntegrityCompetence.alwaysAbstain`                                                   |
| [DQ98]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ99}         | `DecisionQuotient.IntegrityCompetence.alwaysAbstain_integrity`                                         |
| [DQ99]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ100}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_eq_raw_plus_overhead`                         |
| [DQ100]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ101}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_gt_raw_of_evidence`                           |
| [DQ101]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ102}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_of_evidence`                                  |
| [DQ102]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ103}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_of_no_evidence`                               |
| [DQ103]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ104}        | `DecisionQuotient.IntegrityCompetence.claim_admissible_abstain`                                        |
| [DQ104]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ105}        | `DecisionQuotient.IntegrityCompetence.claim_admissible_epsilon_iff`                                    |
| [DQ105]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ106}        | `DecisionQuotient.IntegrityCompetence.claim_admissible_exact_iff`                                      |
| [DQ106]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ107}        | `DecisionQuotient.IntegrityCompetence.claim_admissible_of_evidence`                                    |
| [DQ107]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ108}        | `DecisionQuotient.IntegrityCompetence.competence_implies_integrity`                                    |
| [DQ108]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ109}        | `DecisionQuotient.IntegrityCompetence.competent_has_coverage`                                          |
| [DQ109]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ110}        | `DecisionQuotient.IntegrityCompetence.completion_fraction_defined_of_declared_bound`                   |
| [DQ110]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ111}        | `DecisionQuotient.IntegrityCompetence.epsilon_admissible_iff_raw_lt_certifiedTotal`                    |
| [DQ111]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ112}        | `DecisionQuotient.IntegrityCompetence.epsilon_competence_implies_integrity`                            |
| [DQ112]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ113}        | `DecisionQuotient.IntegrityCompetence.evidence_nonempty_iff_claim_admissible`                          |
| [DQ113]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ114}        | `DecisionQuotient.IntegrityCompetence.evidence_of_claim_admissible`                                    |
| [DQ114]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ115}        | `DecisionQuotient.IntegrityCompetence.exactCertaintyInflation_iff_no_exact_competence`                 |
| [DQ115]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ116}        | `DecisionQuotient.IntegrityCompetence.exact_admissible_iff_raw_lt_certifiedTotal`                      |
| [DQ116]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ117}        | `DecisionQuotient.IntegrityCompetence.exact_claim_admissible_iff_exact_evidence_nonempty`              |
| [DQ117]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ118}        | `DecisionQuotient.IntegrityCompetence.exact_claim_requires_evidence`                                   |
| [DQ118]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ119}        | `DecisionQuotient.IntegrityCompetence.exact_raw_eq_certifiedTotal_iff_exactCertaintyInflation`         |
| [DQ119]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ120}        | `DecisionQuotient.IntegrityCompetence.exact_raw_only_of_no_exact_admissible`                           |
| [DQ120]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ121}        | `DecisionQuotient.IntegrityCompetence.inducedRelation`                                                 |
| [DQ121]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ122}        | `DecisionQuotient.IntegrityCompetence.integrity_forces_abstention`                                     |
| [DQ122]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ123}        | `DecisionQuotient.IntegrityCompetence.integrity_not_competent_of_nonempty_scope`                       |
| [DQ123]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ124}        | `DecisionQuotient.IntegrityCompetence.integrity_resource_bound`                                        |
| [DQ124]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ125}        | `DecisionQuotient.IntegrityCompetence.no_completion_fraction_without_declared_bound`                   |
| [DQ125]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ126}        | `DecisionQuotient.IntegrityCompetence.no_uncertified_epsilon_claim`                                    |
| [DQ126]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ127}        | `DecisionQuotient.IntegrityCompetence.no_uncertified_exact_claim`                                      |
| [DQ127]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ128}        | `DecisionQuotient.IntegrityCompetence.overModelVerdict`                                                |
| [DQ128]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ129}        | `DecisionQuotient.IntegrityCompetence.overModelVerdict_inadmissible_iff`                               |
| [DQ129]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ130}        | `DecisionQuotient.IntegrityCompetence.overModelVerdict_irrational_iff`                                 |
| [DQ130]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ131}        | `DecisionQuotient.IntegrityCompetence.overModelVerdict_rational_iff`                                   |
| [DQ131]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ132}        | `DecisionQuotient.IntegrityCompetence.percentZero`                                                     |
| [DQ132]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ133}        | `DecisionQuotient.IntegrityCompetence.program_framed_as_solver`                                        |
| [DQ133]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ134}        | `DecisionQuotient.IntegrityCompetence.report_admissible_implies_raw_lt_certifiedTotal`                 |
| [DQ134]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ135}        | `DecisionQuotient.IntegrityCompetence.report_not_admissible_implies_raw_eq_certifiedTotal`             |
| [DQ135]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ136}        | `DecisionQuotient.IntegrityCompetence.report_raw_eq_certifiedTotal_iff_certaintyInflation`             |
| [DQ136]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ137}        | `DecisionQuotient.IntegrityCompetence.rlffBaseReward`                                                  |
| [DQ137]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ138}        | `DecisionQuotient.IntegrityCompetence.rlffReward`                                                      |
| [DQ138]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ139}        | `DecisionQuotient.IntegrityCompetence.rlffReward_abstain`                                              |
| [DQ139]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ140}        | `DecisionQuotient.IntegrityCompetence.rlffReward_of_evidence`                                          |
| [DQ140]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ141}        | `DecisionQuotient.IntegrityCompetence.rlffReward_of_no_evidence`                                       |
| [DQ141]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ142}        | `DecisionQuotient.IntegrityCompetence.rlff_abstain_strictly_prefers_no_certificates`                   |
| [DQ142]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ143}        | `DecisionQuotient.IntegrityCompetence.rlff_maximizer_has_evidence`                                     |
| [DQ143]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ144}        | `DecisionQuotient.IntegrityCompetence.rlff_maximizer_is_admissible`                                    |
| [DQ144]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ145}        | `DecisionQuotient.IntegrityCompetence.self_reflected_confidence_not_certification`                     |
| [DQ145]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ146}        | `DecisionQuotient.IntegrityCompetence.signal_certified_positive_implies_admissible`                    |
| [DQ146]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ147}        | `DecisionQuotient.IntegrityCompetence.signal_consistent_of_claim_admissible`                           |
| [DQ147]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ148}        | `DecisionQuotient.IntegrityCompetence.signal_exact_no_competence_forces_zero_certified`                |
| [DQ148]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ149}        | `DecisionQuotient.IntegrityCompetence.signal_no_evidence_forces_zero_certified`                        |
| [DQ149]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ150}        | `DecisionQuotient.IntegrityCompetence.solverIntegrity_substrate_parametric`                            |
| [DQ150]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ151}        | `DecisionQuotient.IntegrityCompetence.solverOfPartialMap`                                              |
| [DQ151]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ152}        | `DecisionQuotient.IntegrityCompetence.solverOfPartialMap_integrity`                                    |
| [DQ152]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ153}        | `DecisionQuotient.IntegrityCompetence.steps_run_scalar_always_defined`                                 |
| [DQ153]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ154}        | `DecisionQuotient.IntegrityCompetence.steps_run_scalar_falsifiable`                                    |
| [DQ154]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ155}        | `DecisionQuotient.IntegrityCompetence.zero_epsilon_competence_iff_exact`                               |
| [DQ155]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ156}        | `DecisionQuotient.InteriorVerification.CoordScore`                                                     |
| [DQ156]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ157}        | `DecisionQuotient.InteriorVerification.GoalClass`                                                      |
| [DQ157]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ158}        | `DecisionQuotient.InteriorVerification.InteriorDominanceVerifiable`                                    |
| [DQ158]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ159}        | `DecisionQuotient.InteriorVerification.TautologicalSetIdentifiable`                                    |
| [DQ159]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ160}        | `DecisionQuotient.InteriorVerification.agreeOnSet`                                                     |
| [DQ160]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ161}        | `DecisionQuotient.InteriorVerification.interiorParetoDominates`                                        |
| [DQ161]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ162}        | `DecisionQuotient.InteriorVerification.interior_certificate_implies_non_rejection`                     |
| [DQ162]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ163}        | `DecisionQuotient.InteriorVerification.interior_dominance_implies_universal_non_rejection`             |
| [DQ163]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ164}        | `DecisionQuotient.InteriorVerification.interior_dominance_not_full_sufficiency`                        |
| [DQ164]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ165}        | `DecisionQuotient.InteriorVerification.interior_verification_tractable_certificate`                    |
| [DQ165]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ166}        | `DecisionQuotient.InteriorVerification.not_sufficientOnSet_of_counterexample`                          |
| [DQ166]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ167}        | `DecisionQuotient.InteriorVerification.singleton_coordinate_interior_certificate`                      |
| [DQ167]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ168}        | `DecisionQuotient.IsPolynomialTime`                                                                    |
| [DQ168]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ169}        | `DecisionQuotient.Literal`                                                                             |
| [DQ169]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ170}        | `DecisionQuotient.MinSufficientSetInstance`                                                            |
| [DQ170]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ171}        | `DecisionQuotient.Outside`                                                                             |
| [DQ171]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ172}        | `DecisionQuotient.PhysicalBudgetCrossover.EncodingSizeModel`                                           |
| [DQ172]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ173}        | `DecisionQuotient.PhysicalBudgetCrossover.ExplicitInfeasible`                                          |
| [DQ173]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ174}        | `DecisionQuotient.PhysicalBudgetCrossover.ExplicitUnbounded`                                           |
| [DQ174]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ175}        | `DecisionQuotient.PhysicalBudgetCrossover.HasCrossover`                                                |
| [DQ175]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ176}        | `DecisionQuotient.PhysicalBudgetCrossover.SuccinctBoundedBy`                                           |
| [DQ176]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ177}        | `DecisionQuotient.PhysicalBudgetCrossover.SuccinctFeasible`                                            |
| [DQ177]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ178}        | `DecisionQuotient.PhysicalBudgetCrossover.crossover_for_all_budgets_above_cap`                         |
| [DQ178]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ179}        | `DecisionQuotient.PhysicalBudgetCrossover.crossover_hardness_bundle`                                   |
| [DQ179]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ180}        | `DecisionQuotient.PhysicalBudgetCrossover.crossover_integrity_policy`                                  |
| [DQ180]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ181}        | `DecisionQuotient.PhysicalBudgetCrossover.has_crossover_of_bounded_succinct_unbounded_explicit`        |
| [DQ181]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ182}        | `DecisionQuotient.PhysicalBudgetCrossover.has_crossover_of_witness`                                    |
| [DQ182]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ183}        | `DecisionQuotient.Physics.Instantiation.Configuration`                                                 |
| [DQ183]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ184}        | `DecisionQuotient.Physics.Instantiation.DecisionCircuit`                                               |
| [DQ184]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ185}        | `DecisionQuotient.Physics.Instantiation.DecisionInterpretation`                                        |
| [DQ185]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ186}        | `DecisionQuotient.Physics.Instantiation.EnergyLandscape`                                               |
| [DQ186]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ187}        | `DecisionQuotient.Physics.Instantiation.LandauerBound`                                                 |
| [DQ187]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ188}        | `DecisionQuotient.Physics.Instantiation.Molecule`                                                      |
| [DQ188]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ189}        | `DecisionQuotient.Physics.Instantiation.MoleculeAsCircuit`                                             |
| [DQ189]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ190}        | `DecisionQuotient.Physics.Instantiation.MoleculeAsDecisionCircuit`                                     |
| [DQ190]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ192}        | `DecisionQuotient.Physics.Instantiation.Reaction`                                                      |
| [DQ192]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ193}        | `DecisionQuotient.Physics.Instantiation.k_Boltzmann`                                                   |
| [DQ193]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ194}        | `DecisionQuotient.PolyReduction`                                                                       |
| [DQ194]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ195}        | `DecisionQuotient.PolyTimeApprox`                                                                      |
| [DQ195]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ196}        | `DecisionQuotient.PolytimeElicitationMechanism`                                                        |
| [DQ196]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ197}        | `DecisionQuotient.Prior`                                                                               |
| [DQ197]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ198}        | `DecisionQuotient.ProductSpace`                                                                        |
| [DQ198]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ199}        | `DecisionQuotient.QBFState`                                                                            |
| [DQ199]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ200}        | `DecisionQuotient.QueryAlgorithm`                                                                      |
| [DQ200]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ201}        | `DecisionQuotient.QueryTranscript`                                                                     |
| [DQ201]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ202}        | `DecisionQuotient.SAT3Instance`                                                                        |
| [DQ202]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ203}        | `DecisionQuotient.SAT3Instance.eval`                                                                   |
| [DQ203]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ204}        | `DecisionQuotient.SAT3Instance.eval_eq_true_iff`                                                       |
| [DQ204]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ205}        | `DecisionQuotient.SAT3Instance.satisfiable`                                                            |
| [DQ205]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ206}        | `DecisionQuotient.SAT3Instance.satisfiedBy`                                                            |
| [DQ206]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ207}        | `DecisionQuotient.SeparableUtility`                                                                    |
| [DQ207]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ208}        | `DecisionQuotient.SetComparisonInstance`                                                               |
| [DQ208]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ209}        | `DecisionQuotient.SharpSATInstance`                                                                    |
| [DQ209]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ210}        | `DecisionQuotient.Sigma2PHardness.GadgetState`                                                         |
| [DQ210]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ211}        | `DecisionQuotient.Sigma2PHardness.I_eq_I_of_encodeX`                                                   |
| [DQ211]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ212}        | `DecisionQuotient.Sigma2PHardness.I_of_encodeX_subset`                                                 |
| [DQ212]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ213}        | `DecisionQuotient.Sigma2PHardness.I_of_x`                                                              |
| [DQ213]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ214}        | `DecisionQuotient.Sigma2PHardness.I_of_x_card`                                                         |
| [DQ214]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ215}        | `DecisionQuotient.Sigma2PHardness.bit`                                                                 |
| [DQ215]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ216}        | `DecisionQuotient.Sigma2PHardness.bit_le_one`                                                          |
| [DQ216]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ217}        | `DecisionQuotient.Sigma2PHardness.bit_lt_two`                                                          |
| [DQ217]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ218}        | `DecisionQuotient.Sigma2PHardness.cCoord`                                                              |
| [DQ218]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ219}        | `DecisionQuotient.Sigma2PHardness.cCoord_inj`                                                          |
| [DQ219]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ220}        | `DecisionQuotient.Sigma2PHardness.cCoord_inj_bits`                                                     |
| [DQ220]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ221}        | `DecisionQuotient.Sigma2PHardness.cCoord_injective`                                                    |
| [DQ221]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ222}        | `DecisionQuotient.Sigma2PHardness.cCoord_val`                                                          |
| [DQ222]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ223}        | `DecisionQuotient.Sigma2PHardness.cCoord_val_lt_of_lt`                                                 |
| [DQ223]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ224}        | `DecisionQuotient.Sigma2PHardness.disjoint_I_of_x00_x11`                                               |
| [DQ224]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ225}        | `DecisionQuotient.Sigma2PHardness.encodeX`                                                             |
| [DQ225]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ226}        | `DecisionQuotient.Sigma2PHardness.encodeX_I_of_x`                                                      |
| [DQ226]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ227}        | `DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant`                                           |
| [DQ227]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ228}        | `DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant_iff_mem_relevant`                          |
| [DQ228]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ229}        | `DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`  |
| [DQ229]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ230}        | `DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant_implies_representationGap_zero`            |
| [DQ230]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ231}        | `DecisionQuotient.Sigma2PHardness.goodEq`                                                              |
| [DQ231]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ232}        | `DecisionQuotient.Sigma2PHardness.goodEq_x00`                                                          |
| [DQ232]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ233}        | `DecisionQuotient.Sigma2PHardness.goodEq_x11`                                                          |
| [DQ233]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ234}        | `DecisionQuotient.Sigma2PHardness.mem_I_of_x_iff`                                                      |
| [DQ234]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ235}        | `DecisionQuotient.Sigma2PHardness.mem_relevantFinset_iff`                                              |
| [DQ235]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ236}        | `DecisionQuotient.Sigma2PHardness.min_representationGap_zero_iff_relevant_card`                        |
| [DQ236]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ237}        | `DecisionQuotient.Sigma2PHardness.min_sufficient_set_iff_relevant_card`                                |
| [DQ237]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ238}        | `DecisionQuotient.Sigma2PHardness.not_goodEq_x01`                                                      |
| [DQ238]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ239}        | `DecisionQuotient.Sigma2PHardness.not_sufficient_of_missing_relevantFinset`                            |
| [DQ239]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ240}        | `DecisionQuotient.Sigma2PHardness.relevantFinset`                                                      |
| [DQ240]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ241}        | `DecisionQuotient.Sigma2PHardness.representationGap`                                                   |
| [DQ241]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ242}        | `DecisionQuotient.Sigma2PHardness.representationGap_eq_waste_plus_missing`                             |
| [DQ242]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ243}        | `DecisionQuotient.Sigma2PHardness.representationGap_eq_zero_iff`                                       |
| [DQ243]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ244}        | `DecisionQuotient.Sigma2PHardness.representationGap_missing_eq_gapCard`                                |
| [DQ244]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ245}        | `DecisionQuotient.Sigma2PHardness.representationGap_zero_iff_exactlyIdentifiesRelevant`                |
| [DQ245]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ246}        | `DecisionQuotient.Sigma2PHardness.representationGap_zero_iff_minimalSufficient`                        |
| [DQ246]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ247}        | `DecisionQuotient.Sigma2PHardness.representationGap_zero_iff_sufficient_and_subset_relevantFinset`     |
| [DQ247]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ248}        | `DecisionQuotient.Sigma2PHardness.representationGap_zero_implies_sufficient`                           |
| [DQ248]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ249}        | `DecisionQuotient.Sigma2PHardness.sufficient_iff_relevantFinset_subset`                                |
| [DQ249]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ250}        | `DecisionQuotient.Sigma2PHardness.sufficient_iff_relevant_subset`                                      |
| [DQ250]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ251}        | `DecisionQuotient.Sigma2PHardness.sufficient_of_contains_relevant`                                     |
| [DQ251]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ252}        | `DecisionQuotient.Sigma2PHardness.two_mul_add_one_lt_two_mul`                                          |
| [DQ252]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ253}        | `DecisionQuotient.Sigma2PHardness.univ_sufficient_bool`                                                |
| [DQ253]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ254}        | `DecisionQuotient.Sigma2PHardness.validI`                                                              |
| [DQ254]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ255}        | `DecisionQuotient.Sigma2PHardness.validI_I_of_x`                                                       |
| [DQ255]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ256}        | `DecisionQuotient.Sigma2PHardness.validI_iff_exists_x`                                                 |
| [DQ256]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ257}        | `DecisionQuotient.Sigma2PHardness.vector1_obstruction`                                                 |
| [DQ257]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ258}        | `DecisionQuotient.Sigma2PHardness.x00`                                                                 |
| [DQ258]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ259}        | `DecisionQuotient.Sigma2PHardness.x01`                                                                 |
| [DQ259]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ260}        | `DecisionQuotient.Sigma2PHardness.x11`                                                                 |
| [DQ260]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ261}        | `DecisionQuotient.Sigma2PHardness.yCoord`                                                              |
| [DQ261]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ262}        | `DecisionQuotient.Sigma2PHardness.yCoord_val`                                                          |
| [DQ262]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ263}        | `DecisionQuotient.Signal`                                                                              |
| [DQ263]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ264}        | `DecisionQuotient.StateAbstraction`                                                                    |
| [DQ264]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ265}        | `DecisionQuotient.StateBatchQuery`                                                                     |
| [DQ265]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ266}        | `DecisionQuotient.StructuredUtility`                                                                   |
| [DQ266]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ267}        | `DecisionQuotient.SufficiencyCheckInstance`                                                            |
| [DQ267]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ268}        | `DecisionQuotient.SufficiencyInstance`                                                                 |
| [DQ268]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ269}        | `DecisionQuotient.Summary.bounded_actions_tractable`                                                   |
| [DQ269]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ270}        | `DecisionQuotient.Summary.complexity_dichotomy`                                                        |
| [DQ270]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ271}        | `DecisionQuotient.Summary.conp_completeness`                                                           |
| [DQ271]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ272}        | `DecisionQuotient.Summary.eth_lower_bound`                                                             |
| [DQ272]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ273}        | `DecisionQuotient.Summary.min_sufficient_inapproximability`                                            |
| [DQ273]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ274}        | `DecisionQuotient.Summary.parameterized_results`                                                       |
| [DQ274]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ275}        | `DecisionQuotient.Summary.separable_utility_tractable`                                                 |
| [DQ275]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ276}        | `DecisionQuotient.Summary.sharp_p_hardness`                                                            |
| [DQ276]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ277}        | `DecisionQuotient.Summary.tractability_tightness`                                                      |
| [DQ277]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ278}        | `DecisionQuotient.Summary.tree_structure_tractable`                                                    |
| [DQ278]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ279}        | `DecisionQuotient.ThermodynamicLift.ThermoModel`                                                       |
| [DQ279]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ280}        | `DecisionQuotient.ThermodynamicLift.carbonLowerBound`                                                  |
| [DQ280]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ281}        | `DecisionQuotient.ThermodynamicLift.carbon_lower_additive`                                             |
| [DQ281]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ282}        | `DecisionQuotient.ThermodynamicLift.carbon_lower_from_bits_lower`                                      |
| [DQ282]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ283}        | `DecisionQuotient.ThermodynamicLift.carbon_lower_mandatory`                                            |
| [DQ283]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ284}        | `DecisionQuotient.ThermodynamicLift.energyLowerBound`                                                  |
| [DQ284]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ285}        | `DecisionQuotient.ThermodynamicLift.energy_lower_additive`                                             |
| [DQ285]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ286}        | `DecisionQuotient.ThermodynamicLift.energy_lower_from_bits_lower`                                      |
| [DQ286]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ287}        | `DecisionQuotient.ThermodynamicLift.energy_lower_mandatory`                                            |
| [DQ287]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ288}        | `DecisionQuotient.ThermodynamicLift.eventual_thermo_lift`                                              |
| [DQ288]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ289}        | `DecisionQuotient.ThermodynamicLift.hardness_thermo_bundle_conditional`                                |
| [DQ289]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ290}        | `DecisionQuotient.ThermodynamicLift.mandatory_conserved_bundle_conditional`                            |
| [DQ290]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ291}        | `DecisionQuotient.ThermodynamicLift.mandatory_cost_bundle`                                             |
| [DQ291]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ292}        | `DecisionQuotient.TreeStructured`                                                                      |
| [DQ292]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ293}        | `DecisionQuotient.UniverseDynamics`                                                                    |
| [DQ293]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ294}        | `DecisionQuotient.ValueQueryState`                                                                     |
| [DQ294]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ295}        | `DecisionQuotient.actions_card`                                                                        |
| [DQ295]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ296}        | `DecisionQuotient.adversarialOpt`                                                                      |
| [DQ296]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ297}        | `DecisionQuotient.adversarialOpt_eq_false_of_ne`                                                       |
| [DQ297]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ298}        | `DecisionQuotient.adversarialOpt_eq_true_of_eq`                                                        |
| [DQ298]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ299}        | `DecisionQuotient.agreeOn`                                                                             |
| [DQ299]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ300}        | `DecisionQuotient.agreeOn_flipAt`                                                                      |
| [DQ300]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ301}        | `DecisionQuotient.agreeOn_iff_subset_agreementSet`                                                     |
| [DQ301]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ302}        | `DecisionQuotient.agreeOn_xCoords_iff`                                                                 |
| [DQ302]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ303}        | `DecisionQuotient.agreementSet`                                                                        |
| [DQ303]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ304}        | `DecisionQuotient.all_coords_relevant_of_not_tautology`                                                |
| [DQ304]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ305}        | `DecisionQuotient.anchor_sufficiency_sigma2p`                                                          |
| [DQ305]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ306}        | `DecisionQuotient.anchor_sufficiency_sigma2p_nonempty`                                                 |
| [DQ306]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ307}        | `DecisionQuotient.anchoredSlice`                                                                       |
| [DQ307]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ308}        | `DecisionQuotient.anchoredSliceEquivOutside`                                                           |
| [DQ308]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ309}        | `DecisionQuotient.anchoredSlice_mul_fixed_eq_full`                                                     |
| [DQ309]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ310}        | `DecisionQuotient.approxWithin`                                                                        |
| [DQ310]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ311}        | `DecisionQuotient.bestExpectedUtility`                                                                 |
| [DQ311]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ312}        | `DecisionQuotient.bool_minimalSufficient_unique`                                                       |
| [DQ312]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ313}        | `DecisionQuotient.bool_sufficient_erase_irrelevant`                                                    |
| [DQ313]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ314}        | `DecisionQuotient.bounded_actions_complexity`                                                          |
| [DQ314]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ315}        | `DecisionQuotient.bounded_actions_polynomial_time`                                                     |
| [DQ315]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ316}        | `DecisionQuotient.buildDQProblem`                                                                      |
| [DQ316]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ317}        | `DecisionQuotient.card_anchoredSlice`                                                                  |
| [DQ317]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ318}        | `DecisionQuotient.card_anchoredSlice_eq_pow_sub`                                                       |
| [DQ318]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ319}        | `DecisionQuotient.card_anchoredSlice_eq_uniform`                                                       |
| [DQ319]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ320}        | `DecisionQuotient.card_binary_state`                                                                   |
| [DQ320]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ321}        | `DecisionQuotient.card_function_space`                                                                 |
| [DQ321]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ322}        | `DecisionQuotient.card_outside_eq_sub`                                                                 |
| [DQ322]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ323}        | `DecisionQuotient.certificate_lower_bound_for_I`                                                       |
| [DQ323]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ324}        | `DecisionQuotient.certificate_lower_bound_for_I_card`                                                  |
| [DQ324]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ325}        | `DecisionQuotient.certificate_lower_bound_for_I_card_summary`                                          |
| [DQ325]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ326}        | `DecisionQuotient.certificate_lower_bound_for_I_empty`                                                 |
| [DQ326]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ327}        | `DecisionQuotient.certificate_lower_bound_for_I_empty_summary`                                         |
| [DQ327]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ328}        | `DecisionQuotient.certificate_lower_bound_for_I_summary`                                               |
| [DQ328]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ329}        | `DecisionQuotient.certificate_lower_bound_poly`                                                        |
| [DQ329]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ330}        | `DecisionQuotient.certificate_lower_bound_poly_ge`                                                     |
| [DQ330]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ331}        | `DecisionQuotient.certificate_lower_bound_poly_ge_summary`                                             |
| [DQ331]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ332}        | `DecisionQuotient.certificate_lower_bound_poly_summary`                                                |
| [DQ332]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ333}        | `DecisionQuotient.compatibleStates`                                                                    |
| [DQ333]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ334}        | `DecisionQuotient.complexity_summary`                                                                  |
| [DQ334]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ335}        | `DecisionQuotient.constTrueFinite_empty_sufficient`                                                    |
| [DQ335]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ336}        | `DecisionQuotient.constTrueProblem`                                                                    |
| [DQ336]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ337}        | `DecisionQuotient.constTrueProblemFinite`                                                              |
| [DQ337]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ338}        | `DecisionQuotient.constTrueProblemFinite_opt`                                                          |
| [DQ338]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ339}        | `DecisionQuotient.constTrueProblem_opt`                                                                |
| [DQ339]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ340}        | `DecisionQuotient.constTrue_empty_sufficient`                                                          |
| [DQ340]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ341}        | `DecisionQuotient.const_vs_scaled_opt_view_equal`                                                      |
| [DQ341]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ342}        | `DecisionQuotient.const_vs_scaled_value_entry_diff_at_true`                                            |
| [DQ342]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ343}        | `DecisionQuotient.constant_opt_no_relevant`                                                            |
| [DQ343]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ344}        | `DecisionQuotient.constant_opt_quotientSize_one`                                                       |
| [DQ344]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ345}        | `DecisionQuotient.countSatisfyingAssignments`                                                          |
| [DQ345]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ346}        | `DecisionQuotient.countedCheckPairs`                                                                   |
| [DQ346]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ347}        | `DecisionQuotient.countedCheckPairs_steps_bound`                                                       |
| [DQ347]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ348}        | `DecisionQuotient.countedCompare`                                                                      |
| [DQ348]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ349}        | `DecisionQuotient.countedOptEqual`                                                                     |
| [DQ349]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ350}        | `DecisionQuotient.covers`                                                                              |
| [DQ350]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ351}        | `DecisionQuotient.covers_iff_agreeOn`                                                                  |
| [DQ351]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ352}        | `DecisionQuotient.cube_lt_pow`                                                                         |
| [DQ352]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ353}        | `DecisionQuotient.cubic_step_bound`                                                                    |
| [DQ353]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ354}        | `DecisionQuotient.cyclic_dependencies_coNP_hard`                                                       |
| [DQ354]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ355}        | `DecisionQuotient.decisionQuotient_cases`                                                              |
| [DQ355]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ356}        | `DecisionQuotient.decision_quotient_FPTAS`                                                             |
| [DQ356]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ357}        | `DecisionQuotient.decision_quotient_sharp_P_hard`                                                      |
| [DQ357]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ358}        | `DecisionQuotient.decode_error_sum_two_labels`                                                         |
| [DQ358]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ359}        | `DecisionQuotient.dichotomy_by_relevant_size`                                                          |
| [DQ359]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ360}        | `DecisionQuotient.distinguish_requires_target`                                                         |
| [DQ360]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ361}        | `DecisionQuotient.dqExact`                                                                             |
| [DQ361]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ362}        | `DecisionQuotient.dqProjection`                                                                        |
| [DQ362]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ363}        | `DecisionQuotient.dq_approximation_hard`                                                               |
| [DQ363]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ364}        | `DecisionQuotient.emptySufficiency_query_indistinguishable_pair`                                       |
| [DQ364]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ365}        | `DecisionQuotient.emptySufficiency_query_indistinguishable_pair_finite`                                |
| [DQ365]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ366}        | `DecisionQuotient.emptySufficiency_stateBatch_indistinguishable_pair`                                  |
| [DQ366]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ367}        | `DecisionQuotient.emptySufficiency_valueEntry_indistinguishable_pair`                                  |
| [DQ367]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ368}        | `DecisionQuotient.empty_minimal_sufficient_iff_constant`                                               |
| [DQ368]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ369}        | `DecisionQuotient.endpoints`                                                                           |
| [DQ369]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ370}        | `DecisionQuotient.endpoints_card_le`                                                                   |
| [DQ370]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ371}        | `DecisionQuotient.eth_implies_sat3_exponential`                                                        |
| [DQ371]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ372}        | `DecisionQuotient.eth_lower_bound_informal`                                                            |
| [DQ372]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ373}        | `DecisionQuotient.eth_lower_bound_sufficiency_check`                                                   |
| [DQ373]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ374}        | `DecisionQuotient.exactDQ`                                                                             |
| [DQ374]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ375}        | `DecisionQuotient.exists_coord_not_mem`                                                                |
| [DQ375]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ376}        | `DecisionQuotient.exists_distinct_patterns`                                                            |
| [DQ376]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ377}        | `DecisionQuotient.exists_forall_iff_anchor_sufficient`                                                 |
| [DQ377]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ378}        | `DecisionQuotient.exists_forall_iff_anchor_sufficient_padded`                                          |
| [DQ378]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ379}        | `DecisionQuotient.exists_not_mem_of_card_lt_univ`                                                      |
| [DQ379]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ380}        | `DecisionQuotient.exists_state_not_in_endpoints`                                                       |
| [DQ380]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ381}        | `DecisionQuotient.expectedUtility`                                                                     |
| [DQ381]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ382}        | `DecisionQuotient.exponential_query_complexity`                                                        |
| [DQ382]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ383}        | `DecisionQuotient.feasibleActions`                                                                     |
| [DQ383]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ384}        | `DecisionQuotient.flipAt`                                                                              |
| [DQ384]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ385}        | `DecisionQuotient.flipAt_ne`                                                                           |
| [DQ385]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ386}        | `DecisionQuotient.fptRunningTime`                                                                      |
| [DQ386]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ387}        | `DecisionQuotient.fpt_kernel_bound`                                                                    |
| [DQ387]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ388}        | `DecisionQuotient.full_query_distinguishes_const_spike_finite`                                         |
| [DQ388]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ389}        | `DecisionQuotient.greedy_approximation_ratio`                                                          |
| [DQ389]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ390}        | `DecisionQuotient.hard_when_all_relevant`                                                              |
| [DQ390]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ391}        | `DecisionQuotient.indistinguishable_pair_forces_one_error`                                             |
| [DQ391]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ392}        | `DecisionQuotient.indistinguishable_pair_forces_one_error_per_seed`                                    |
| [DQ392]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ393}        | `DecisionQuotient.infeasible_not_optimal_of_gap`                                                       |
| [DQ393]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ394}        | `DecisionQuotient.lawDecisionProblem`                                                                  |
| [DQ394]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ395}        | `DecisionQuotient.lawUtility`                                                                          |
| [DQ395]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ396}        | `DecisionQuotient.lawUtility_eq_of_allowed_iff`                                                        |
| [DQ396]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ397}        | `DecisionQuotient.logicallyDeterministic`                                                              |
| [DQ397]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ398}        | `DecisionQuotient.mem_compatibleStates_iff`                                                            |
| [DQ398]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ399}        | `DecisionQuotient.mem_optFinset_iff`                                                                   |
| [DQ399]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ400}        | `DecisionQuotient.mem_optimalActions_iff_actionValue`                                                  |
| [DQ400]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ401}        | `DecisionQuotient.mem_xCoords`                                                                         |
| [DQ401]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ402}        | `DecisionQuotient.min_sufficient_W2_hard`                                                              |
| [DQ402]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ403}        | `DecisionQuotient.min_sufficient_inapproximability_informal`                                           |
| [DQ403]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ404}        | `DecisionQuotient.min_sufficient_set_coNP_hard`                                                        |
| [DQ404]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ405}        | `DecisionQuotient.min_sufficient_set_inapprox_statement`                                               |
| [DQ405]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ406}        | `DecisionQuotient.mkState`                                                                             |
| [DQ406]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ407}        | `DecisionQuotient.mkState_castAdd`                                                                     |
| [DQ407]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ408}        | `DecisionQuotient.mkState_natAdd`                                                                      |
| [DQ408]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ409}        | `DecisionQuotient.monotone_opt_at_top`                                                                 |
| [DQ409]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ410}        | `DecisionQuotient.mss_equiv_relevant_card`                                                             |
| [DQ410]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ411}        | `DecisionQuotient.no_satisfying_of_count_zero`                                                         |
| [DQ411]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ412}        | `DecisionQuotient.not_tautology_iff_exists_opt_difference`                                             |
| [DQ412]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ413}        | `DecisionQuotient.numPatterns`                                                                         |
| [DQ413]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ414}        | `DecisionQuotient.optComparisonCost`                                                                   |
| [DQ414]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ415}        | `DecisionQuotient.optFinset`                                                                           |
| [DQ415]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ416}        | `DecisionQuotient.optFinset_subset_projectedOptCover`                                                  |
| [DQ416]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ417}        | `DecisionQuotient.opt_both`                                                                            |
| [DQ417]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ418}        | `DecisionQuotient.opt_eq_feasible_of_gap`                                                              |
| [DQ418]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ419}        | `DecisionQuotient.opt_eq_of_allowed_iff`                                                               |
| [DQ419]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ420}        | `DecisionQuotient.opt_falsifying`                                                                      |
| [DQ420]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ421}        | `DecisionQuotient.opt_falsifying_many`                                                                 |
| [DQ421]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ422}        | `DecisionQuotient.opt_no_only`                                                                         |
| [DQ422]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ423}        | `DecisionQuotient.opt_reference`                                                                       |
| [DQ423]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ424}        | `DecisionQuotient.opt_reference_many`                                                                  |
| [DQ424]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ425}        | `DecisionQuotient.opt_satisfying`                                                                      |
| [DQ425]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ426}        | `DecisionQuotient.opt_singleton_of_logicallyDeterministic`                                             |
| [DQ426]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ427}        | `DecisionQuotient.opt_tautology_many`                                                                  |
| [DQ427]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ428}        | `DecisionQuotient.opt_yes_only`                                                                        |
| [DQ428]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ429}        | `DecisionQuotient.optimalActions_eq_of_separable`                                                      |
| [DQ429]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ430}        | `DecisionQuotient.optimalActions_sat`                                                                  |
| [DQ430]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ431}        | `DecisionQuotient.optimalActions_unsat`                                                                |
| [DQ431]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ432}        | `DecisionQuotient.oracleView`                                                                          |
| [DQ432]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ433}        | `DecisionQuotient.oracleViewFinite`                                                                    |
| [DQ433]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ434}        | `DecisionQuotient.oracleViewFinite_eq_of_agree`                                                        |
| [DQ434]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ435}        | `DecisionQuotient.oracleView_eq_of_agree`                                                              |
| [DQ435]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ436}        | `DecisionQuotient.over_modeling_justified`                                                             |
| [DQ436]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ437}        | `DecisionQuotient.pairCheckCost`                                                                       |
| [DQ437]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ438}        | `DecisionQuotient.parameterized_complexity_summary`                                                    |
| [DQ438]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ439}        | `DecisionQuotient.patternClass`                                                                        |
| [DQ439]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ440}        | `DecisionQuotient.poly_compose_bound`                                                                  |
| [DQ440]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ441}        | `DecisionQuotient.poly_inner_bound`                                                                    |
| [DQ441]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ442}        | `DecisionQuotient.poly_reduction_implies_many_one_exists`                                              |
| [DQ442]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ443}        | `DecisionQuotient.poly_reduction_preserves_P`                                                          |
| [DQ443]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ444}        | `DecisionQuotient.polytime_elicitation_exists_structured`                                              |
| [DQ444]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ445}        | `DecisionQuotient.proj_binary_state`                                                                   |
| [DQ445]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ446}        | `DecisionQuotient.projectToCoords`                                                                     |
| [DQ446]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ447}        | `DecisionQuotient.projectedOptCover`                                                                   |
| [DQ447]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ448}        | `DecisionQuotient.projectedOptCover_eq_opt_of_sufficient`                                              |
| [DQ448]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ449}        | `DecisionQuotient.qbfEval`                                                                             |
| [DQ449]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ450}        | `DecisionQuotient.qbfEval_mkState`                                                                     |
| [DQ450]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ451}        | `DecisionQuotient.qbfProblem`                                                                          |
| [DQ451]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ452}        | `DecisionQuotient.qbfUtility`                                                                          |
| [DQ452]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ453}        | `DecisionQuotient.queryComplexityLowerBound`                                                           |
| [DQ453]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ454}        | `DecisionQuotient.queryDistinguishes`                                                                  |
| [DQ454]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ455}        | `DecisionQuotient.query_lower_bound_statement`                                                         |
| [DQ455]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ456}        | `DecisionQuotient.quotientSize_bool_le_pow`                                                            |
| [DQ456]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ457}        | `DecisionQuotient.quotientSize_le_card`                                                                |
| [DQ457]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ458}        | `DecisionQuotient.quotientSize_le_pow_coords`                                                          |
| [DQ458]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ459}        | `DecisionQuotient.quotientSize_one_all_sufficient`                                                     |
| [DQ459]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ460}        | `DecisionQuotient.quotientSize_one_iff_constant`                                                       |
| [DQ460]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ461}        | `DecisionQuotient.quotientSize_pos`                                                                    |
| [DQ461]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ462}        | `DecisionQuotient.recoverCount`                                                                        |
| [DQ462]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ463}        | `DecisionQuotient.recoverCount_correct`                                                                |
| [DQ463]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ464}        | `DecisionQuotient.reductionProblem`                                                                    |
| [DQ464]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ465}        | `DecisionQuotient.reductionProblemMany`                                                                |
| [DQ465]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ466}        | `DecisionQuotient.reductionUtility`                                                                    |
| [DQ466]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ467}        | `DecisionQuotient.reductionUtilityMany`                                                                |
| [DQ467]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ468}        | `DecisionQuotient.reduction_not_separable`                                                             |
| [DQ468]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ469}        | `DecisionQuotient.replace_proj_other`                                                                  |
| [DQ469]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ470}        | `DecisionQuotient.replace_proj_self`                                                                   |
| [DQ470]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ471}        | `DecisionQuotient.sameProjection`                                                                      |
| [DQ471]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ472}        | `DecisionQuotient.sameProjection_trans`                                                                |
| [DQ472]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ473}        | `DecisionQuotient.sat3ToCircuit`                                                                       |
| [DQ473]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ474}        | `DecisionQuotient.sat3_reduction_size_preserving`                                                      |
| [DQ474]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ475}        | `DecisionQuotient.satSet`                                                                              |
| [DQ475]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ476}        | `DecisionQuotient.satSet_empty_of_count_zero`                                                          |
| [DQ476]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ477}        | `DecisionQuotient.scaledTrueProblem`                                                                   |
| [DQ477]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ478}        | `DecisionQuotient.scaledTrueProblem_opt`                                                               |
| [DQ478]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ479}        | `DecisionQuotient.separable_isSufficient`                                                              |
| [DQ479]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ480}        | `DecisionQuotient.sharpSAT_encoded_in_DQ`                                                              |
| [DQ480]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ481}        | `DecisionQuotient.sharpSAT_exactDQ`                                                                    |
| [DQ481]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ482}        | `DecisionQuotient.sharpSATtoDQ`                                                                        |
| [DQ482]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ483}        | `DecisionQuotient.sharpSATtoDQInstance`                                                                |
| [DQ483]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ484}        | `DecisionQuotient.single_action_always_sufficient`                                                     |
| [DQ484]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ485}        | `DecisionQuotient.someEmbedding`                                                                       |
| [DQ485]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ486}        | `DecisionQuotient.spikeFinite_empty_not_sufficient`                                                    |
| [DQ486]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ487}        | `DecisionQuotient.spikeProblem`                                                                        |
| [DQ487]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ488}        | `DecisionQuotient.spikeProblemFinite`                                                                  |
| [DQ488]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ489}        | `DecisionQuotient.spikeProblemFinite_opt_at`                                                           |
| [DQ489]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ490}        | `DecisionQuotient.spikeProblemFinite_opt_off`                                                          |
| [DQ490]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ491}        | `DecisionQuotient.spikeProblem_opt_at`                                                                 |
| [DQ491]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ492}        | `DecisionQuotient.spikeProblem_opt_off`                                                                |
| [DQ492]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ493}        | `DecisionQuotient.spike_empty_not_sufficient`                                                          |
| [DQ493]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ494}        | `DecisionQuotient.stateBatchView`                                                                      |
| [DQ494]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ495}        | `DecisionQuotient.stateBatchView_eq_if_hidden_untouched`                                               |
| [DQ495]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ496}        | `DecisionQuotient.structured_isSufficient`                                                             |
| [DQ496]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ497}        | `DecisionQuotient.succ_cube`                                                                           |
| [DQ497]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ498}        | `DecisionQuotient.sufficiencyToSetComparison`                                                          |
| [DQ498]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ499}        | `DecisionQuotient.sufficiency_FPT_coords`                                                              |
| [DQ499]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ500}        | `DecisionQuotient.sufficiency_W1_hard_unbounded_actions`                                               |
| [DQ500]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ501}        | `DecisionQuotient.sufficiency_check_coNP_hard`                                                         |
| [DQ501]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ502}        | `DecisionQuotient.sufficiency_check_polynomial`                                                        |
| [DQ502]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ503}        | `DecisionQuotient.sufficiency_iff_dq_ratio`                                                            |
| [DQ503]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ504}        | `DecisionQuotient.sufficiency_iff_projectedOptCover_eq_opt`                                            |
| [DQ504]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ505}        | `DecisionQuotient.sufficiency_in_P`                                                                    |
| [DQ505]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ506}        | `DecisionQuotient.sufficiency_poly_bounded_actions`                                                    |
| [DQ506]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ507}        | `DecisionQuotient.sufficiency_poly_separable`                                                          |
| [DQ507]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ508}        | `DecisionQuotient.sufficiency_poly_tree_structured`                                                    |
| [DQ508]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ509}        | `DecisionQuotient.sufficient_implies_tautology`                                                        |
| [DQ509]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ510}        | `DecisionQuotient.sufficient_implies_tautology_many`                                                   |
| [DQ510]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ511}        | `DecisionQuotient.sufficient_means_factorizable`                                                       |
| [DQ511]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ512}        | `DecisionQuotient.sufficient_of_projectedOptCover_eq_opt`                                              |
| [DQ512]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ513}        | `DecisionQuotient.sufficient_preserves_decisions`                                                      |
| [DQ513]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ514}        | `DecisionQuotient.targetProblem`                                                                       |
| [DQ514]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ515}        | `DecisionQuotient.targetProblem_opt_off_target`                                                        |
| [DQ515]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ516}        | `DecisionQuotient.targetProblem_opt_on_target`                                                         |
| [DQ516]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ517}        | `DecisionQuotient.targetProblems_agree_outside`                                                        |
| [DQ517]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ518}        | `DecisionQuotient.tautology_iff_opt_constant`                                                          |
| [DQ518]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ519}        | `DecisionQuotient.tautology_iff_sufficient`                                                            |
| [DQ519]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ520}        | `DecisionQuotient.tautology_iff_sufficient_many`                                                       |
| [DQ520]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ521}        | `DecisionQuotient.tautology_implies_sufficient`                                                        |
| [DQ521]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ522}        | `DecisionQuotient.tautology_implies_sufficient_many`                                                   |
| [DQ522]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ523}        | `DecisionQuotient.totalCheckCost`                                                                      |
| [DQ523]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ524}        | `DecisionQuotient.totalCheckCost_le_pow`                                                               |
| [DQ524]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ525}        | `DecisionQuotient.touchedStates`                                                                       |
| [DQ525]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ526}        | `DecisionQuotient.touchedStates_card_le_query_card`                                                    |
| [DQ526]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ527}        | `DecisionQuotient.tractability_conditions_tight`                                                       |
| [DQ527]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ528}        | `DecisionQuotient.tractable_small_state_space`                                                         |
| [DQ528]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ529}        | `DecisionQuotient.tractable_when_few_relevant`                                                         |
| [DQ529]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ530}        | `DecisionQuotient.two_actions_coNP_hard`                                                               |
| [DQ530]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ531}        | `DecisionQuotient.two_le_one_false`                                                                    |
| [DQ531]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ532}        | `DecisionQuotient.two_le_zero_false`                                                                   |
| [DQ532]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ533}        | `DecisionQuotient.two_state_sufficiency`                                                               |
| [DQ533]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ534}        | `DecisionQuotient.unique_matching_pattern`                                                             |
| [DQ534]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ535}        | `DecisionQuotient.universe_sets_objective_schema`                                                      |
| [DQ535]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ536}        | `DecisionQuotient.valueEntryView`                                                                      |
| [DQ536]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ537}        | `DecisionQuotient.valueEntryView_eq_if_hidden_untouched`                                               |
| [DQ537]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ538}        | `DecisionQuotient.valueEntryView_eq_of_stateBatchView_eq_on_touched`                                   |
| [DQ538]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ539}        | `DecisionQuotient.valueOfInformation`                                                                  |
| [DQ539]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ540}        | `DecisionQuotient.valueOfInformation_const`                                                            |
| [DQ540]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ541}        | `DecisionQuotient.vectorB_blocked`                                                                     |
| [DQ541]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ542}        | `DecisionQuotient.voi_computation_sharp_P_hard`                                                        |
| [DQ542]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ543}        | `DecisionQuotient.voi_fptas_smooth_utilities`                                                          |
| [DQ543]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ544}        | `DecisionQuotient.weightedQueryCost`                                                                   |
| [DQ544]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ545}        | `DecisionQuotient.weightedQueryCost_ge_min_mul_card`                                                   |
| [DQ545]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ546}        | `DecisionQuotient.weightedQueryCost_ge_min_mul_of_card_lb`                                             |
| [DQ546]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ547}        | `DecisionQuotient.weighted_seed_error_identity`                                                        |
| [DQ547]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ548}        | `DecisionQuotient.weighted_seed_half_floor`                                                            |
| [DQ548]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ549}        | `DecisionQuotient.xCoords`                                                                             |
| [DQ549]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ550}        | `DecisionQuotient.xPart`                                                                               |
| [DQ550]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ551}        | `DecisionQuotient.xPart_mkState`                                                                       |
| [DQ551]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ552}        | `DecisionQuotient.yAllFalse`                                                                           |
| [DQ552]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ553}        | `DecisionQuotient.yAllFalse_mkState`                                                                   |
| [DQ553]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ554}        | `DecisionQuotient.yPart`                                                                               |
| [DQ554]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ555}        | `DecisionQuotient.yPart_mkState`                                                                       |
| [DQ555]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ556}        | `DecisionQuotient.Physics.Instantiation.Circuit`                                                       |
| [DQ556]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ557}        | `DecisionQuotient.Physics.Instantiation.Dynamics`                                                      |
| [DQ557]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ558}        | `DecisionQuotient.Physics.Instantiation.Geometry`                                                      |
| [DQ558]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ559}        | `DecisionQuotient.Physics.Instantiation.MoleculeCircuit`                                               |
| [DQ559]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ560}        | `DecisionQuotient.Physics.Instantiation.MoleculeDynamics`                                              |
| [DQ560]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ561}        | `DecisionQuotient.Physics.Instantiation.MoleculeGeometry`                                              |
| [DQ561]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ562}        | `DecisionQuotient.Physics.Instantiation.geometry_plus_dynamics_is_circuit`                             |
| [DQ562]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ563}        | `DecisionQuotient.Physics.Instantiation.law_objective_schema`                                          |
| [DQ563]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ564}        | `DecisionQuotient.Physics.Instantiation.law_opt_eq_feasible_of_gap`                                    |
| [DQ564]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ565}        | `DecisionQuotient.Physics.Instantiation.law_opt_singleton_of_deterministic`                            |
| [DQ565]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:F1}           | `Formula.eval`                                                                                         |
| [F1]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:F2}           | `Formula.isTautology`                                                                                  |
| [F2]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:F3}           | `Formula.majorityTrue`                                                                                 |
| [F3]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:GC1}          | `GoalClass.classMonotoneOn`                                                                            |
| [GC1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:GC2}          | `GoalClass.isNonNegativelyTautologicalCoord`                                                           |
| [GC2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:GC3}          | `GoalClass.isTautologicalCoord`                                                                        |
| [GC3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:GC4}          | `GoalClass.tautologicalSet`                                                                            |
| [GC4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD1}          | `DecisionQuotient.HardnessDistribution.centralization_dominance_bundle`                                |
| [HD1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD2}          | `DecisionQuotient.HardnessDistribution.centralization_step_saves_n_minus_one`                          |
| [HD2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD3}          | `DecisionQuotient.HardnessDistribution.centralized_higher_leverage`                                    |
| [HD3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD4}          | `DecisionQuotient.HardnessDistribution.complete_model_dominates_after_threshold`                       |
| [HD4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD5}          | `DecisionQuotient.HardnessDistribution.gap_conservation_card`                                          |
| [HD5]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD6}          | `DecisionQuotient.HardnessDistribution.generalizedTotal_with_saturation_eventually_constant`           |
| [HD6]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD7}          | `DecisionQuotient.HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`       |
| [HD7]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD8}          | `DecisionQuotient.HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`            |
| [HD8]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD9}          | `DecisionQuotient.HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower` |
| [HD9]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD10}         | `DecisionQuotient.HardnessDistribution.generalized_right_eventually_dominates_wrong`                   |
| [HD10]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD11}         | `DecisionQuotient.HardnessDistribution.hardnessEfficiency_eq_central_share`                            |
| [HD11]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD12}         | `DecisionQuotient.HardnessDistribution.isRightHardness`                                                |
| [HD12]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD13}         | `DecisionQuotient.HardnessDistribution.isWrongHardness`                                                |
| [HD13]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD14}         | `DecisionQuotient.HardnessDistribution.linear_lt_exponential_plus_constant_eventually`                 |
| [HD14]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD15}         | `DecisionQuotient.HardnessDistribution.native_dominates_manual`                                        |
| [HD15]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD16}         | `DecisionQuotient.HardnessDistribution.no_positive_slope_linear_represents_saturating`                 |
| [HD16]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD17}         | `DecisionQuotient.HardnessDistribution.right_dominates_wrong`                                          |
| [HD17]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD18}         | `DecisionQuotient.HardnessDistribution.saturatingSiteCost_eventually_constant`                         |
| [HD18]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD19}         | `DecisionQuotient.HardnessDistribution.simplicityTax_grows`                                            |
| [HD19]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD20}         | `DecisionQuotient.HardnessDistribution.totalDOF_eventually_constant_iff_zero_distributed`              |
| [HD20]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD21}         | `DecisionQuotient.HardnessDistribution.totalDOF_ge_intrinsic`                                          |
| [HD21]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC1}          | `DecisionQuotient.IntegrityCompetence.CertaintyInflation`                                              |
| [IC1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC2}          | `DecisionQuotient.IntegrityCompetence.CompletionFractionDefined`                                       |
| [IC2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC3}          | `DecisionQuotient.IntegrityCompetence.EvidenceForReport`                                               |
| [IC3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC4}          | `DecisionQuotient.IntegrityCompetence.ExactCertaintyInflation`                                         |
| [IC4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC5}          | `DecisionQuotient.IntegrityCompetence.Percent`                                                         |
| [IC5]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC6}          | `DecisionQuotient.IntegrityCompetence.RLFFWeights`                                                     |
| [IC6]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC7}          | `DecisionQuotient.IntegrityCompetence.ReportSignal`                                                    |
| [IC7]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC8}          | `DecisionQuotient.IntegrityCompetence.ReportBitModel`                                                  |
| [IC8]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC9}          | `DecisionQuotient.IntegrityCompetence.SignalConsistent`                                                |
| [IC9]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC10}         | `DecisionQuotient.IntegrityCompetence.admissible_irrational_strictly_more_than_rational`               |
| [IC10]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC11}         | `DecisionQuotient.IntegrityCompetence.admissible_matrix_counts`                                        |
| [IC11]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC12}         | `DecisionQuotient.IntegrityCompetence.abstain_signal_exists_with_guess_self`                           |
| [IC12]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC13}         | `DecisionQuotient.IntegrityCompetence.certaintyInflation_iff_not_admissible`                           |
| [IC13]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC14}         | `DecisionQuotient.IntegrityCompetence.certificationOverheadBits`                                       |
| [IC14]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC15}         | `DecisionQuotient.IntegrityCompetence.certificationOverheadBits_of_evidence`                           |
| [IC15]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC16}         | `DecisionQuotient.IntegrityCompetence.certificationOverheadBits_of_no_evidence`                        |
| [IC16]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC17}         | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits`                                              |
| [IC17]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC18}         | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_ge_raw`                                       |
| [IC18]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IPT1}         | `IsPolynomialTime.const`                                                                               |
| [IPT1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IPT2}         | `IsPolynomialTime.of_steps_le`                                                                         |
| [IPT2]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IW1}          | `InsufficiencyWitness.certifies_not_sufficient`                                                        |
| [IW1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IW2}          | `InsufficiencyWitness.not_abstract_sufficient`                                                         |
| [IW2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L1}           | `ExactPhysicalClaimWellTyped`                                                                          |
| [L1]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L2}           | `ExcusedBy`                                                                                            |
| [L2]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L3}           | `ExplicitHardnessAssumptions`                                                                          |
| [L3]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L4}           | `Literal.eval`                                                                                         |
| [L4]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L5}           | `OneStepSequentialObjective`                                                                           |
| [L5]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L6}           | `RegimeSimulation`                                                                                     |
| [L6]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L7}           | `StandardComplexityAssumptions`                                                                        |
| [L7]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L8}           | `StochasticCriterionObjective`                                                                         |
| [L8]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L9}           | `StructureDetectable`                                                                                  |
| [L9]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L10}          | `TransitionCoupledObjective`                                                                           |
| [L10]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L11}          | `TwoStepObjective`                                                                                     |
| [L11]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L12}          | `adq`                                                                                                  |
| [L12]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L13}          | `adq_ordering`                                                                                         |
| [L13]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L14}          | `agentBridgeClass`                                                                                     |
| [L14]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L15}          | `agent_transfer_licensed_iff_snapshot`                                                                 |
| [L15]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L16}          | `anchor_sigma2p_complete_conditional`                                                                  |
| [L16]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L17}          | `anchor_sigma2p_reduction_core`                                                                        |
| [L17]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L18}          | `boundaryCharacterized`                                                                                |
| [L18]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L19}          | `boundaryCharacterized_iff_exists_sufficient_subset`                                                   |
| [L19]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L20}          | `bounded_actions_detectable`                                                                           |
| [L20]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L21}          | `bounded_actions_reusable_heuristic`                                                                   |
| [L21]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L22}          | `bridgeFailureWitness`                                                                                 |
| [L22]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L23}          | `boolHypercube_node_count`                                                                             |
| [L23]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L24}          | `bridgeTransferLicensed`                                                                               |
| [L24]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L25}          | `bridge_boundary_represented_family`                                                                   |
| [L25]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L26}          | `bridge_failure_witness_non_one_step`                                                                  |
| [L26]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L27}          | `bridge_transfer_iff_one_step_class`                                                                   |
| [L27]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L28}          | `certified_total_bits_split_core`                                                                      |
| [L28]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L29}          | `constantBoolDP`                                                                                       |
| [L29]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L30}          | `constantBoolDP_empty_sufficient`                                                                      |
| [L30]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L31}          | `constantBoolDP_opt`                                                                                   |
| [L31]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L32}          | `cost_asymmetry_eth_conditional`                                                                       |
| [L32]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L33}          | `declaredRegimeFamily`                                                                                 |
| [L33]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L34}          | `declaredRegimeFamily_complete`                                                                        |
| [L34]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L35}          | `declared_physics_no_universal_exact_certifier_core`                                                   |
| [L35]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L36}          | `dichotomy_conditional`                                                                                |
| [L36]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L37}          | `epsilon_admissible_iff_raw_lt_certified_total_core`                                                   |
| [L37]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L38}          | `exact_admissible_iff_raw_lt_certified_total_core`                                                     |
| [L38]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L39}          | `exact_certainty_inflation_under_hardness_core`                                                        |
| [L39]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L40}          | `exact_raw_eq_certified_iff_certainty_inflation_core`                                                  |
| [L40]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L41}          | `exact_raw_only_of_no_exact_admissible_core`                                                           |
| [L41]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L42}          | `explicit_assumptions_required_of_not_excused_core`                                                    |
| [L42]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L43}          | `explicit_state_upper_core`                                                                            |
| [L43]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L44}          | `firstCoordDP`                                                                                         |
| [L44]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L45}          | `firstCoordDP_empty_not_sufficient`                                                                    |
| [L45]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L46}          | `firstCoordDP_opt`                                                                                     |
| [L46]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L47}          | `hard_family_all_coords_core`                                                                          |
| [L47]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L48}          | `horizonTwoWitness`                                                                                    |
| [L48]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L49}          | `horizonTwoWitness_immediate_empty_sufficient`                                                         |
| [L49]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L50}          | `horizonTwoWitness_not_empty_sufficient_two_step`                                                      |
| [L50]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L51}          | `horizon_gt_one_bridge_can_fail_on_sufficiency`                                                        |
| [L51]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L52}          | `i0`                                                                                                   |
| [L52]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L53}          | `i0_bridge`                                                                                            |
| [L53]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L54}          | `information_barrier_opt_oracle_core`                                                                  |
| [L54]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L55}          | `information_barrier_state_batch_core`                                                                 |
| [L55]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L56}          | `information_barrier_value_entry_core`                                                                 |
| [L56]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L57}          | `integrity_resource_bound_for_sufficiency`                                                             |
| [L57]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L58}          | `integrity_universal_applicability_core`                                                               |
| [L58]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L59}          | `minsuff_collapse_core`                                                                                |
| [L59]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L60}          | `minsuff_collapse_to_conp_conditional`                                                                 |
| [L60]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L61}          | `minsuff_conp_complete_conditional`                                                                    |
| [L61]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L62}          | `no_auto_minimize_of_p_neq_conp`                                                                       |
| [L62]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L63}          | `no_exact_claim_admissible_under_hardness_core`                                                        |
| [L63]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L64}          | `no_exact_claim_under_declared_assumptions_unless_excused_core`                                        |
| [L64]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L65}          | `no_exact_identifier_implies_not_boundary_characterized`                                               |
| [L65]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L66}          | `no_uncertified_exact_claim_core`                                                                      |
| [L66]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L67}          | `node_count_does_not_determine_edge_geometry`                                                          |
| [L67]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L68}          | `one_step_bridge`                                                                                      |
| [L68]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L69}          | `oracle_lattice_transfer_as_regime_simulation`                                                         |
| [L69]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L70}          | `physical_crossover_above_cap_core`                                                                    |
| [L70]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L71}          | `physical_crossover_core`                                                                              |
| [L71]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L72}          | `physical_crossover_hardness_core`                                                                     |
| [L72]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L73}          | `physical_crossover_policy_core`                                                                       |
| [L73]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L74}          | `preferTrueSelector`                                                                                   |
| [L74]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L75}          | `process_bridge_failure_witness`                                                                       |
| [L75]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L76}          | `query_obstruction_boolean_corollary`                                                                  |
| [L76]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L77}          | `query_obstruction_finite_state_core`                                                                  |
| [L77]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L78}          | `regimeCoreClaim`                                                                                      |
| [L78]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L79}          | `regime_core_claim_proved`                                                                             |
| [L79]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L80}          | `regime_simulation_transfers_hardness`                                                                 |
| [L80]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L81}          | `reusable_heuristic_of_detectable`                                                                     |
| [L81]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L82}          | `s0_bridge`                                                                                            |
| [L82]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L83}          | `s1_bridge`                                                                                            |
| [L83]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L84}          | `sFalse`                                                                                               |
| [L84]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L85}          | `sTrue`                                                                                                |
| [L85]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L86}          | `selectorGapProblem`                                                                                   |
| [L86]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L87}          | `selectorGap_not_set_sufficient_empty`                                                                 |
| [L87]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L88}          | `selectorGap_selectorSufficient_empty`                                                                 |
| [L88]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L89}          | `selectorGap_true_mem_opt`                                                                             |
| [L89]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L90}          | `selectorSufficient_not_implies_setSufficient`                                                         |
| [L90]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L91}          | `separable_detectable`                                                                                 |
| [L91]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L92}          | `separable_reusable_heuristic`                                                                         |
| [L92]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L93}          | `snapshot_vs_process_typed_boundary`                                                                   |
| [L93]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L94}          | `standard_assumption_ledger_unpack`                                                                    |
| [L94]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L95}          | `stochasticWitness`                                                                                    |
| [L95]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L96}          | `stochastic_objective_bridge_can_fail_on_sufficiency`                                                  |
| [L96]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L97}          | `structureDetectable_of_decidable`                                                                     |
| [L97]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L98}          | `subproblem_hardness_lifts_to_full`                                                                    |
| [L98]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L99}          | `subproblem_transfer_as_regime_simulation`                                                             |
| [L99]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L100}         | `sufficiency_conp_complete_conditional`                                                                |
| [L100]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L101}         | `sufficiency_conp_reduction_core`                                                                      |
| [L101]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L102}         | `thermo_conservation_additive_core`                                                                    |
| [L102]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L103}         | `thermo_energy_carbon_lift_core`                                                                       |
| [L103]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L104}         | `thermo_eventual_lift_core`                                                                            |
| [L104]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L105}         | `thermo_hardness_bundle_core`                                                                          |
| [L105]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L106}         | `thermo_mandatory_cost_core`                                                                           |
| [L106]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L107}         | `tractable_bounded_core`                                                                               |
| [L107]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L108}         | `tractable_separable_core`                                                                             |
| [L108]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L109}         | `tractable_subcases_conditional`                                                                       |
| [L109]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L110}         | `tractable_tree_core`                                                                                  |
| [L110]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L111}         | `transitionWitness`                                                                                    |
| [L111]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L112}         | `transition_coupled_bridge_can_fail_on_sufficiency`                                                    |
| [L112]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L113}         | `tree_reusable_heuristic`                                                                              |
| [L113]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L114}         | `tree_structure_detectable`                                                                            |
| [L114]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L115}         | `typed_claim_admissibility_core`                                                                       |
| [L115]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L116}         | `typed_static_class_completeness`                                                                      |
| [L116]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L117}         | `universal_solver_framing_core`                                                                        |
| [L117]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:MC1}          | `MatrixCell.verdict`                                                                                   |
| [MC1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:MC2}          | `MatrixCell.verdict_substrate_independent`                                                             |
| [MC2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:OSSO1}        | `OneStepSequentialObjective.Opt`                                                                       |
| [OSSO1]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:OSSO2}        | `OneStepSequentialObjective.isSufficient`                                                              |
| [OSSO2]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:OSSO3}        | `OneStepSequentialObjective.toDecisionProblem`                                                         |
| [OSSO3]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS1}        | `Paper4bStochasticSequential.Assignment`                                                               |
| [P4SS1]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS10}       | `Paper4bStochasticSequential.ClaimClosure.claim_trajectory_substrate_dependent`                        |
| [P4SS10]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS100}      | `Paper4bStochasticSequential.bounded_horizon_tractable_rigorous`                                       |
| [P4SS100]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS101}      | `Paper4bStochasticSequential.bounded_support_tractable_rigorous`                                       |
| [P4SS101]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS102}      | `Paper4bStochasticSequential.card_stochAction`                                                         |
| [P4SS102]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS103}      | `Paper4bStochasticSequential.card_stochState`                                                          |
| [P4SS103]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS104}      | `Paper4bStochasticSequential.coinFlips`                                                                |
| [P4SS104]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS105}      | `Paper4bStochasticSequential.coinFlips_product`                                                        |
| [P4SS105]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS106}      | `Paper4bStochasticSequential.composeReduction4b`                                                       |
| [P4SS106]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS107}      | `Paper4bStochasticSequential.costlySignal`                                                             |
| [P4SS107]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS108}      | `Paper4bStochasticSequential.countedBoundedHorizonSufficiency`                                         |
| [P4SS108]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS109}      | `Paper4bStochasticSequential.countedBoundedHorizonSufficiency_steps`                                   |
| [P4SS109]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS11}       | `Paper4bStochasticSequential.ClaimClosure.claim_verdict_substrate_independent`                         |
| [P4SS11]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS110}      | `Paper4bStochasticSequential.countedBoundedSupportCheck`                                               |
| [P4SS110]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS111}      | `Paper4bStochasticSequential.countedBoundedSupportCheck_steps`                                         |
| [P4SS111]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS112}      | `Paper4bStochasticSequential.countedExpectedUtility`                                                   |
| [P4SS112]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS113}      | `Paper4bStochasticSequential.countedExpectedUtility_steps`                                             |
| [P4SS113]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS114}      | `Paper4bStochasticSequential.countedIsOptimal`                                                         |
| [P4SS114]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS115}      | `Paper4bStochasticSequential.countedIsOptimal_steps`                                                   |
| [P4SS115]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS116}      | `Paper4bStochasticSequential.countedIsRelevantCoord`                                                   |
| [P4SS116]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS117}      | `Paper4bStochasticSequential.countedIsRelevantCoord_steps`                                             |
| [P4SS117]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS118}      | `Paper4bStochasticSequential.countedProductSufficiencyCheck`                                           |
| [P4SS118]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS119}      | `Paper4bStochasticSequential.countedProductSufficiencyCheck_steps`                                     |
| [P4SS119]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS12}       | `Paper4bStochasticSequential.ClaimClosure.timeComplexity'`                                             |
| [P4SS12]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS120}      | `Paper4bStochasticSequential.countedStochOptEqual`                                                     |
| [P4SS120]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS121}      | `Paper4bStochasticSequential.countedStochSufficiency`                                                  |
| [P4SS121]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS122}      | `Paper4bStochasticSequential.countedStochSufficiency_poly`                                             |
| [P4SS122]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS123}      | `Paper4bStochasticSequential.countedStochasticOpt`                                                     |
| [P4SS123]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS124}      | `Paper4bStochasticSequential.countedStochasticOpt_steps`                                               |
| [P4SS124]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS125}      | `Paper4bStochasticSequential.critical_value_half`                                                      |
| [P4SS125]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS126}      | `Paper4bStochasticSequential.decisionEntropy`                                                          |
| [P4SS126]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS127}      | `Paper4bStochasticSequential.detectSufficiency`                                                        |
| [P4SS127]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS128}      | `Paper4bStochasticSequential.dichotomyThreshold`                                                       |
| [P4SS128]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS129}      | `Paper4bStochasticSequential.diminishing_returns`                                                      |
| [P4SS129]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS13}       | `Paper4bStochasticSequential.ClaimClosure.trajectory`                                                  |
| [P4SS13]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS130}      | `Paper4bStochasticSequential.distributionSupport`                                                      |
| [P4SS130]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS131}      | `Paper4bStochasticSequential.energyTimeTradeoff`                                                       |
| [P4SS131]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS132}      | `Paper4bStochasticSequential.energyUsed`                                                               |
| [P4SS132]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS133}      | `Paper4bStochasticSequential.entropy`                                                                  |
| [P4SS133]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS134}      | `Paper4bStochasticSequential.equilibriumPrice`                                                         |
| [P4SS134]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS135}      | `Paper4bStochasticSequential.evidenceMonotoneRetraction`                                               |
| [P4SS135]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS136}      | `Paper4bStochasticSequential.executeCountedQuery`                                                      |
| [P4SS136]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS137}      | `Paper4bStochasticSequential.executeStrategy`                                                          |
| [P4SS137]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS138}      | `Paper4bStochasticSequential.expectedQueryComplexity`                                                  |
| [P4SS138]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS139}      | `Paper4bStochasticSequential.expectedUtilityAfterObservation`                                          |
| [P4SS139]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS14}       | `Paper4bStochasticSequential.ClaimSequence`                                                            |
| [P4SS14]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS140}      | `Paper4bStochasticSequential.expectedUtility_via_marginals`                                            |
| [P4SS140]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS141}      | `Paper4bStochasticSequential.expectedValue`                                                            |
| [P4SS141]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS142}      | `Paper4bStochasticSequential.extractPolicy`                                                            |
| [P4SS142]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS143}      | `Paper4bStochasticSequential.extractableWork`                                                          |
| [P4SS143]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS144}      | `Paper4bStochasticSequential.full_compression_when_sufficient`                                         |
| [P4SS144]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS145}      | `Paper4bStochasticSequential.fully_observable_tractable_rigorous`                                      |
| [P4SS145]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS146}      | `Paper4bStochasticSequential.gamblerSequential`                                                        |
| [P4SS146]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS147}      | `Paper4bStochasticSequential.hardFamily`                                                               |
| [P4SS147]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS148}      | `Paper4bStochasticSequential.hard_family_complexity`                                                   |
| [P4SS148]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS149}      | `Paper4bStochasticSequential.heatDissipated`                                                           |
| [P4SS149]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS15}       | `Paper4bStochasticSequential.ClaimWithEvidence`                                                        |
| [P4SS15]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS150}      | `Paper4bStochasticSequential.heuristic_transfer`                                                       |
| [P4SS150]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS151}      | `Paper4bStochasticSequential.horizon_gt_one_can_fail`                                                  |
| [P4SS151]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS152}      | `Paper4bStochasticSequential.info_sufficient_implies_stochastic`                                       |
| [P4SS152]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS153}      | `Paper4bStochasticSequential.informationSufficient`                                                    |
| [P4SS153]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS154}      | `Paper4bStochasticSequential.integrity_competence_verdict_independent`                                 |
| [P4SS154]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS155}      | `Paper4bStochasticSequential.inventoryMDP`                                                             |
| [P4SS155]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS156}      | `Paper4bStochasticSequential.inventoryMDP_fully_observable`                                            |
| [P4SS156]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS157}      | `Paper4bStochasticSequential.isProbabilityDistribution`                                                |
| [P4SS157]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS158}      | `Paper4bStochasticSequential.isProductDistribution`                                                    |
| [P4SS158]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS159}      | `Paper4bStochasticSequential.isRelevantCoord`                                                          |
| [P4SS159]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS16}       | `Paper4bStochasticSequential.ComplexityClass`                                                          |
| [P4SS16]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS160}      | `Paper4bStochasticSequential.kappa_sufficient_statistic`                                               |
| [P4SS160]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS161}      | `Paper4bStochasticSequential.landauerConstant`                                                         |
| [P4SS161]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS162}      | `Paper4bStochasticSequential.landauer_limit`                                                           |
| [P4SS162]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS163}      | `Paper4bStochasticSequential.majsat_implies_sufficient`                                                |
| [P4SS163]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS164}      | `Paper4bStochasticSequential.marginalValue`                                                            |
| [P4SS164]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS165}      | `Paper4bStochasticSequential.maxExpectedUtility`                                                       |
| [P4SS165]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS166}      | `Paper4bStochasticSequential.mdpValueIteration`                                                        |
| [P4SS166]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS167}      | `Paper4bStochasticSequential.mdpValueIterationStep`                                                    |
| [P4SS167]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS168}      | `Paper4bStochasticSequential.mdpValueIterationStep_steps`                                              |
| [P4SS168]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS169}      | `Paper4bStochasticSequential.mdpValueIteration_steps`                                                  |
| [P4SS169]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS17}       | `Paper4bStochasticSequential.CountedQueryAlgorithm`                                                    |
| [P4SS17]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS170}      | `Paper4bStochasticSequential.more_energy_faster`                                                       |
| [P4SS170]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS171}      | `Paper4bStochasticSequential.mutualInfoCoordAction`                                                    |
| [P4SS171]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS172}      | `Paper4bStochasticSequential.noRetractionWithoutEvidence`                                              |
| [P4SS172]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS173}      | `Paper4bStochasticSequential.no_arbitrage`                                                             |
| [P4SS173]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS174}      | `Paper4bStochasticSequential.optimalAlgo'`                                                             |
| [P4SS174]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS175}      | `Paper4bStochasticSequential.perturbationDistribution`                                                 |
| [P4SS175]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS176}      | `Paper4bStochasticSequential.perturbedStochProblem`                                                    |
| [P4SS176]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS177}      | `Paper4bStochasticSequential.phaseTransitionParam`                                                     |
| [P4SS177]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS178}      | `Paper4bStochasticSequential.policyFromHistory`                                                        |
| [P4SS178]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS179}      | `Paper4bStochasticSequential.posterior`                                                                |
| [P4SS179]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS18}       | `Paper4bStochasticSequential.Distribution`                                                             |
| [P4SS18]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS180}      | `Paper4bStochasticSequential.posterior_uniform_prior`                                                  |
| [P4SS180]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS181}      | `Paper4bStochasticSequential.pp_decide_correct`                                                        |
| [P4SS181]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS182}      | `Paper4bStochasticSequential.probSufficient`                                                           |
| [P4SS182]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS183}      | `Paper4bStochasticSequential.product_distribution_tractable_rigorous`                                  |
| [P4SS183]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS184}      | `Paper4bStochasticSequential.query_computation_tradeoff`                                               |
| [P4SS184]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS185}      | `Paper4bStochasticSequential.query_lower_bound_insufficient`                                           |
| [P4SS185]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS186}      | `Paper4bStochasticSequential.query_lower_bound_sufficient`                                             |
| [P4SS186]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS187}      | `Paper4bStochasticSequential.randomStochProblem`                                                       |
| [P4SS187]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS188}      | `Paper4bStochasticSequential.reduceMAJSAT`                                                             |
| [P4SS188]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS189}      | `Paper4bStochasticSequential.reduceMAJSAT_correct`                                                     |
| [P4SS189]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS19}       | `Paper4bStochasticSequential.Distribution.delta`                                                       |
| [P4SS19]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS190}      | `Paper4bStochasticSequential.reduceMAJSAT_hard`                                                        |
| [P4SS190]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS191}      | `Paper4bStochasticSequential.reduceMAJSAT_poly`                                                        |
| [P4SS191]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS192}      | `Paper4bStochasticSequential.reduceMAJSAT_polytime`                                                    |
| [P4SS192]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS193}      | `Paper4bStochasticSequential.reduceTQBF`                                                               |
| [P4SS193]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS194}      | `Paper4bStochasticSequential.reduceTQBF_correct`                                                       |
| [P4SS194]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS195}      | `Paper4bStochasticSequential.reduceTQBF_hard`                                                          |
| [P4SS195]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS196}      | `Paper4bStochasticSequential.reduceTQBF_poly`                                                          |
| [P4SS196]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS197}      | `Paper4bStochasticSequential.reduction_hardness_transfer`                                              |
| [P4SS197]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS198}      | `Paper4bStochasticSequential.refinement_strengthens`                                                   |
| [P4SS198]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS199}      | `Paper4bStochasticSequential.regime_hierarchy`                                                         |
| [P4SS199]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS2}        | `Paper4bStochasticSequential.BigO`                                                                     |
| [P4SS2]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS20}       | `Paper4bStochasticSequential.Distribution.probability`                                                 |
| [P4SS20]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS200}      | `Paper4bStochasticSequential.relevantCoordSize`                                                        |
| [P4SS200]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS201}      | `Paper4bStochasticSequential.relevant_coord_concentration`                                             |
| [P4SS201]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS202}      | `Paper4bStochasticSequential.retraction_with_evidence_preserves`                                       |
| [P4SS202]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS203}      | `Paper4bStochasticSequential.retraction_without_evidence_violates`                                     |
| [P4SS203]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS204}      | `Paper4bStochasticSequential.reversibleSufficiencyAlgo`                                                |
| [P4SS204]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS205}      | `Paper4bStochasticSequential.reversible_lower_cost`                                                    |
| [P4SS205]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS206}      | `Paper4bStochasticSequential.seqProblem`                                                               |
| [P4SS206]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS207}      | `Paper4bStochasticSequential.sequentialDecisionEquiv`                                                  |
| [P4SS207]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS208}      | `Paper4bStochasticSequential.sequentialQueryComplexity`                                                |
| [P4SS208]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS209}      | `Paper4bStochasticSequential.sequentialValue`                                                          |
| [P4SS209]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS21}       | `Paper4bStochasticSequential.Distribution.uniform`                                                     |
| [P4SS21]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS210}      | `Paper4bStochasticSequential.sequential_complexity`                                                    |
| [P4SS210]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS211}      | `Paper4bStochasticSequential.sequential_not_stochastic`                                                |
| [P4SS211]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS212}      | `Paper4bStochasticSequential.sequential_query_bounded_horizon`                                         |
| [P4SS212]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS213}      | `Paper4bStochasticSequential.sequential_sufficiency_pspace_complete`                                   |
| [P4SS213]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS214}      | `Paper4bStochasticSequential.sequential_sufficiency_pspace_hard`                                       |
| [P4SS214]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS215}      | `Paper4bStochasticSequential.sequential_sufficient_in_PSPACE`                                          |
| [P4SS215]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS216}      | `Paper4bStochasticSequential.signal_cost_lower_when_sufficient`                                        |
| [P4SS216]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS217}      | `Paper4bStochasticSequential.smoothedComplexity`                                                       |
| [P4SS217]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS218}      | `Paper4bStochasticSequential.smoothed_easier_than_worst`                                               |
| [P4SS218]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS219}      | `Paper4bStochasticSequential.someAction`                                                               |
| [P4SS219]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS22}       | `Paper4bStochasticSequential.Distribution.uniformList`                                                 |
| [P4SS22]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS220}      | `Paper4bStochasticSequential.static_complexity`                                                        |
| [P4SS220]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS221}      | `Paper4bStochasticSequential.static_subset_stochastic`                                                 |
| [P4SS221]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS222}      | `Paper4bStochasticSequential.static_to_sequential_transfer`                                            |
| [P4SS222]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS223}      | `Paper4bStochasticSequential.static_to_stochastic_can_fail`                                            |
| [P4SS223]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS224}      | `Paper4bStochasticSequential.static_to_stochastic_transfer`                                            |
| [P4SS224]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS225}      | `Paper4bStochasticSequential.stochDistribution`                                                        |
| [P4SS225]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS226}      | `Paper4bStochasticSequential.stochProblem`                                                             |
| [P4SS226]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS227}      | `Paper4bStochasticSequential.stochUtility`                                                             |
| [P4SS227]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS228}      | `Paper4bStochasticSequential.stoch_opt_falsifying`                                                     |
| [P4SS228]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS229}      | `Paper4bStochasticSequential.stoch_opt_reference`                                                      |
| [P4SS229]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS23}       | `Paper4bStochasticSequential.Evidence`                                                                 |
| [P4SS23]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS230}      | `Paper4bStochasticSequential.stoch_opt_satisfying`                                                     |
| [P4SS230]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS231}      | `Paper4bStochasticSequential.stochaEnumAlgo`                                                           |
| [P4SS231]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS232}      | `Paper4bStochasticSequential.stochaEnumAlgo_optimal`                                                   |
| [P4SS232]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS233}      | `Paper4bStochasticSequential.stochaPPDecide`                                                           |
| [P4SS233]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS234}      | `Paper4bStochasticSequential.stochasticCompressionRatio`                                               |
| [P4SS234]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS235}      | `Paper4bStochasticSequential.stochasticDecisionEquiv`                                                  |
| [P4SS235]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS236}      | `Paper4bStochasticSequential.stochasticExpectedUtility`                                                |
| [P4SS236]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS237}      | `Paper4bStochasticSequential.stochastic_complexity`                                                    |
| [P4SS237]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS238}      | `Paper4bStochasticSequential.stochastic_few_relevant_tractable`                                        |
| [P4SS238]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS239}      | `Paper4bStochasticSequential.stochastic_many_relevant_hard`                                            |
| [P4SS239]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS24}       | `Paper4bStochasticSequential.Identifiable`                                                             |
| [P4SS24]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS240}      | `Paper4bStochasticSequential.stochastic_not_static`                                                    |
| [P4SS240]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS241}      | `Paper4bStochasticSequential.stochastic_query_product`                                                 |
| [P4SS241]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS242}      | `Paper4bStochasticSequential.stochastic_quotient_factors`                                              |
| [P4SS242]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS243}      | `Paper4bStochasticSequential.stochastic_sufficiency_pp_complete`                                       |
| [P4SS243]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS244}      | `Paper4bStochasticSequential.stochastic_sufficiency_pp_hard`                                           |
| [P4SS244]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS245}      | `Paper4bStochasticSequential.stochastic_sufficient_in_PP`                                              |
| [P4SS245]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS246}      | `Paper4bStochasticSequential.stochastic_sufficient_not_info`                                           |
| [P4SS246]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS247}      | `Paper4bStochasticSequential.stochastic_to_sequential_can_fail`                                        |
| [P4SS247]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS248}      | `Paper4bStochasticSequential.stochastic_to_sequential_transfer`                                        |
| [P4SS248]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS249}      | `Paper4bStochasticSequential.substrateCost`                                                            |
| [P4SS249]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS25}       | `Paper4bStochasticSequential.InComplexityClass`                                                        |
| [P4SS25]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS250}      | `Paper4bStochasticSequential.substrate_independence_verdict`                                           |
| [P4SS250]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS251}      | `Paper4bStochasticSequential.sufficient_enables_work_extraction`                                       |
| [P4SS251]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS252}      | `Paper4bStochasticSequential.sufficient_implies_majsat`                                                |
| [P4SS252]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS253}      | `Paper4bStochasticSequential.temporalIntegrity`                                                        |
| [P4SS253]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS254}      | `Paper4bStochasticSequential.temporal_integrity_hardness`                                              |
| [P4SS254]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS255}      | `Paper4bStochasticSequential.thermodynamicCost`                                                        |
| [P4SS255]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS256}      | `Paper4bStochasticSequential.timeComplexity`                                                           |
| [P4SS256]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS257}      | `Paper4bStochasticSequential.timeComplexity''`                                                         |
| [P4SS257]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS258}      | `Paper4bStochasticSequential.toStatic`                                                                 |
| [P4SS258]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS259}      | `Paper4bStochasticSequential.toStochastic`                                                             |
| [P4SS259]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS26}       | `Paper4bStochasticSequential.IsPolyTime`                                                               |
| [P4SS26]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS260}      | `Paper4bStochasticSequential.trajectory`                                                               |
| [P4SS260]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS261}      | `Paper4bStochasticSequential.trajectory_substrate_dependent`                                           |
| [P4SS261]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS262}      | `Paper4bStochasticSequential.umbrellaStatic`                                                           |
| [P4SS262]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS263}      | `Paper4bStochasticSequential.umbrellaStochastic`                                                       |
| [P4SS263]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS264}      | `Paper4bStochasticSequential.umbrella_expected_carry`                                                  |
| [P4SS264]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS265}      | `Paper4bStochasticSequential.uniformDistribution`                                                      |
| [P4SS265]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS266}      | `Paper4bStochasticSequential.uniformStochDistribution`                                                 |
| [P4SS266]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS267}      | `Paper4bStochasticSequential.uniformStochDistribution_valid`                                           |
| [P4SS267]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS268}      | `Paper4bStochasticSequential.uniform_is_valid`                                                         |
| [P4SS268]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS269}      | `Paper4bStochasticSequential.valueIterStep`                                                            |
| [P4SS269]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS27}       | `Paper4bStochasticSequential.MAJSAT_pp_complete`                                                       |
| [P4SS27]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS270}      | `Paper4bStochasticSequential.valueIteration`                                                           |
| [P4SS270]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS271}      | `Paper4bStochasticSequential.valueIteration_poly`                                                      |
| [P4SS271]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS272}      | `Paper4bStochasticSequential.valueOfInformation`                                                       |
| [P4SS272]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS273}      | `Paper4bStochasticSequential.voi_positive_when_insufficient`                                           |
| [P4SS273]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS274}      | `Paper4bStochasticSequential.voi_zero_when_sufficient`                                                 |
| [P4SS274]{.sans-serif} |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS28}       | `Paper4bStochasticSequential.MAJSAT_pred`                                                              |
| [P4SS28]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS29}       | `Paper4bStochasticSequential.MatrixCell`                                                               |
| [P4SS29]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS3}        | `Paper4bStochasticSequential.ClaimClosure.PP_bound`                                                    |
| [P4SS3]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS30}       | `Paper4bStochasticSequential.PP_class`                                                                 |
| [P4SS30]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS31}       | `Paper4bStochasticSequential.PSPACE_CLASS`                                                             |
| [P4SS31]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS32}       | `Paper4bStochasticSequential.PSPACE_class`                                                             |
| [P4SS32]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS33}       | `Paper4bStochasticSequential.PTIME`                                                                    |
| [P4SS33]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS34}       | `Paper4bStochasticSequential.Policy`                                                                   |
| [P4SS34]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS35}       | `Paper4bStochasticSequential.PolyReduction4b`                                                          |
| [P4SS35]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS36}       | `Paper4bStochasticSequential.PolynomialSpaceComputable`                                                |
| [P4SS36]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS37}       | `Paper4bStochasticSequential.PolynomialTimeComputable`                                                 |
| [P4SS37]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS38}       | `Paper4bStochasticSequential.ProblemSequence`                                                          |
| [P4SS38]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS39}       | `Paper4bStochasticSequential.ProductDistributionStructure`                                             |
| [P4SS39]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS4}        | `Paper4bStochasticSequential.ClaimClosure.claim_hierarchy`                                             |
| [P4SS4]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS40}       | `Paper4bStochasticSequential.QueryOracle`                                                              |
| [P4SS40]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS41}       | `Paper4bStochasticSequential.QueryStrategy`                                                            |
| [P4SS41]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS42}       | `Paper4bStochasticSequential.SequentialDecisionProblem`                                                |
| [P4SS42]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS43}       | `Paper4bStochasticSequential.SequentialQuotientType`                                                   |
| [P4SS43]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS44}       | `Paper4bStochasticSequential.SequentialRegime`                                                         |
| [P4SS44]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS45}       | `Paper4bStochasticSequential.SequentialSufficient`                                                     |
| [P4SS45]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS46}       | `Paper4bStochasticSequential.StaticRegime`                                                             |
| [P4SS46]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS47}       | `Paper4bStochasticSequential.StochInsufficiencyWitness`                                                |
| [P4SS47]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS48}       | `Paper4bStochasticSequential.StochasticDecisionProblem`                                                |
| [P4SS48]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS49}       | `Paper4bStochasticSequential.StochasticQuotientType`                                                   |
| [P4SS49]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS5}        | `Paper4bStochasticSequential.ClaimClosure.claim_many_relevant_hard`                                    |
| [P4SS5]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS50}       | `Paper4bStochasticSequential.StochasticRegime`                                                         |
| [P4SS50]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS51}       | `Paper4bStochasticSequential.StochasticSufficient`                                                     |
| [P4SS51]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS52}       | `Paper4bStochasticSequential.StructureClass`                                                           |
| [P4SS52]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS53}       | `Paper4bStochasticSequential.StructurePrior`                                                           |
| [P4SS53]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS54}       | `Paper4bStochasticSequential.TQBF`                                                                     |
| [P4SS54]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS55}       | `Paper4bStochasticSequential.TQBF_pspace_complete`                                                     |
| [P4SS55]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS56}       | `Paper4bStochasticSequential.Tractability.PP_Complexity`                                               |
| [P4SS56]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS57}       | `Paper4bStochasticSequential.Tractability.PSPACE_Complexity`                                           |
| [P4SS57]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS58}       | `Paper4bStochasticSequential.Tractability.boundedHorizonAlgo`                                          |
| [P4SS58]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS59}       | `Paper4bStochasticSequential.Tractability.boundedSupportAlgo`                                          |
| [P4SS59]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS6}        | `Paper4bStochasticSequential.ClaimClosure.claim_phase_transition`                                      |
| [P4SS6]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS60}       | `Paper4bStochasticSequential.Tractability.bounded_horizon_polynomial`                                  |
| [P4SS60]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS61}       | `Paper4bStochasticSequential.Tractability.bounded_support_polynomial`                                  |
| [P4SS61]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS62}       | `Paper4bStochasticSequential.Tractability.bounded_support_tight`                                       |
| [P4SS62]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS63}       | `Paper4bStochasticSequential.Tractability.coordinateSufficient`                                        |
| [P4SS63]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS64}       | `Paper4bStochasticSequential.Tractability.f`                                                           |
| [P4SS64]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS65}       | `Paper4bStochasticSequential.Tractability.fptTimeComplexity`                                           |
| [P4SS65]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS66}       | `Paper4bStochasticSequential.Tractability.fpt_horizon`                                                 |
| [P4SS66]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS67}       | `Paper4bStochasticSequential.Tractability.fully_observable_polynomial`                                 |
| [P4SS67]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS68}       | `Paper4bStochasticSequential.Tractability.fully_observable_reduces_to_static`                          |
| [P4SS68]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS69}       | `Paper4bStochasticSequential.Tractability.hasBoundedHorizon`                                           |
| [P4SS69]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS7}        | `Paper4bStochasticSequential.ClaimClosure.claim_static_sequential_horizon_one`                         |
| [P4SS7]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS70}       | `Paper4bStochasticSequential.Tractability.hasBoundedSupport`                                           |
| [P4SS70]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS71}       | `Paper4bStochasticSequential.Tractability.isFullyObservable`                                           |
| [P4SS71]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS72}       | `Paper4bStochasticSequential.Tractability.isProductDistribution'`                                      |
| [P4SS72]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS73}       | `Paper4bStochasticSequential.Tractability.mdpAlgo`                                                     |
| [P4SS73]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS74}       | `Paper4bStochasticSequential.Tractability.optimalAlgo`                                                 |
| [P4SS74]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS75}       | `Paper4bStochasticSequential.Tractability.partially_observable_hard`                                   |
| [P4SS75]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS76}       | `Paper4bStochasticSequential.Tractability.productAlgo`                                                 |
| [P4SS76]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS77}       | `Paper4bStochasticSequential.Tractability.product_decomposition`                                       |
| [P4SS77]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS78}       | `Paper4bStochasticSequential.Tractability.product_distribution_polynomial`                             |
| [P4SS78]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS79}       | `Paper4bStochasticSequential.Tractability.product_distribution_tight`                                  |
| [P4SS79]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS8}        | `Paper4bStochasticSequential.ClaimClosure.claim_static_stochastic_product`                             |
| [P4SS8]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS80}       | `Paper4bStochasticSequential.Tractability.remove_bounded_horizon_hard`                                 |
| [P4SS80]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS81}       | `Paper4bStochasticSequential.Tractability.remove_bounded_support_hard`                                 |
| [P4SS81]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS82}       | `Paper4bStochasticSequential.Tractability.remove_full_observability_hard`                              |
| [P4SS82]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS83}       | `Paper4bStochasticSequential.Tractability.remove_product_distribution_hard`                            |
| [P4SS83]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS84}       | `Paper4bStochasticSequential.Tractability.solvesSufficiency`                                           |
| [P4SS84]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS85}       | `Paper4bStochasticSequential.Tractability.timeComplexity`                                              |
| [P4SS85]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS86}       | `Paper4bStochasticSequential.Tractability.toStatic`                                                    |
| [P4SS86]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS87}       | `Paper4bStochasticSequential.Tractability.tractability_conditions_minimal_sequential`                  |
| [P4SS87]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS88}       | `Paper4bStochasticSequential.Tractability.tractability_conditions_minimal_stochastic`                  |
| [P4SS88]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS89}       | `Paper4bStochasticSequential.Tractability.unbounded_horizon_hard`                                      |
| [P4SS89]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS9}        | `Paper4bStochasticSequential.ClaimClosure.claim_stochastic_sequential_memoryless`                      |
| [P4SS9]{.sans-serif}   |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS90}       | `Paper4bStochasticSequential.above_critical_hard`                                                      |
| [P4SS90]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS91}       | `Paper4bStochasticSequential.abstentionSet`                                                            |
| [P4SS91]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS92}       | `Paper4bStochasticSequential.abstention_decreases`                                                     |
| [P4SS92]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS93}       | `Paper4bStochasticSequential.achievable`                                                               |
| [P4SS93]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS94}       | `Paper4bStochasticSequential.argmax`                                                                   |
| [P4SS94]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS95}       | `Paper4bStochasticSequential.averageCaseComplexity`                                                    |
| [P4SS95]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS96}       | `Paper4bStochasticSequential.average_case_hard`                                                        |
| [P4SS96]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS97}       | `Paper4bStochasticSequential.bayesian_update`                                                          |
| [P4SS97]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS98}       | `Paper4bStochasticSequential.below_critical_polynomial`                                                |
| [P4SS98]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:P4SS99}       | `Paper4bStochasticSequential.boundedSupport`                                                           |
| [P4SS99]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PBC1}         | `DecisionQuotient.PhysicalBudgetCrossover.CrossoverAt`                                                 |
| [PBC1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PBC2}         | `DecisionQuotient.PhysicalBudgetCrossover.explicit_infeasible_succinct_feasible_of_crossover`          |
| [PBC2]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC1}          | `PhysicalComplexity.ComputationalRequirement`                                                          |
| [PC1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC2}          | `PhysicalComplexity.InstanceSize`                                                                      |
| [PC2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC3}          | `PhysicalComplexity.Landauer_bound`                                                                    |
| [PC3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC4}          | `PhysicalComplexity.PhysicalComputer`                                                                  |
| [PC4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC5}          | `PhysicalComplexity.bit_energy_cost`                                                                   |
| [PC5]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC6}          | `PhysicalComplexity.coNP_physically_impossible`                                                        |
| [PC6]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC7}          | `PhysicalComplexity.coNP_requirement`                                                                  |
| [PC7]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC8}          | `PhysicalComplexity.k_Boltzmann`                                                                       |
| [PC8]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC9}          | `PhysicalComplexity.sufficiency_physically_impossible`                                                 |
| [PC9]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC10}         | `PhysicalComplexity.AccessRegime.AccessRegime`                                                         |
| [PC10]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC11}         | `PhysicalComplexity.AccessRegime.PhysicalDevice`                                                       |
| [PC11]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC12}         | `PhysicalComplexity.AccessRegime.RegimeEval`                                                           |
| [PC12]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC13}         | `PhysicalComplexity.AccessRegime.RegimeProof`                                                          |
| [PC13]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC14}         | `PhysicalComplexity.AccessRegime.RegimeSample`                                                         |
| [PC14]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC15}         | `PhysicalComplexity.AccessRegime.RegimeWithCertificate`                                                |
| [PC15]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC16}         | `PhysicalComplexity.AccessRegime.certificate_amortizes_hardness`                                       |
| [PC16]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC17}         | `PhysicalComplexity.AccessRegime.certificate_upgrades_regime`                                          |
| [PC17]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC18}         | `PhysicalComplexity.AccessRegime.physical_succinct_certification_hard`                                 |
| [PC18]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC19}         | `PhysicalComplexity.AccessRegime.regime_upgrade_with_certificate`                                      |
| [PC19]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC20}         | `PhysicalComplexity.AccessRegime.AccessChannelLaw`                                                     |
| [PC20]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC21}         | `PhysicalComplexity.AccessRegime.AuditableWithCertificate`                                             |
| [PC21]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC22}         | `PhysicalComplexity.AccessRegime.FiveWayMeet`                                                          |
| [PC22]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC23}         | `PhysicalComplexity.AccessRegime.HardUnderEval`                                                        |
| [PC23]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC24}         | `PhysicalComplexity.AccessRegime.RegimeEvalOn`                                                         |
| [PC24]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC25}         | `PhysicalComplexity.AccessRegime.RegimeProofOn`                                                        |
| [PC25]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC26}         | `PhysicalComplexity.AccessRegime.RegimeSampleOn`                                                       |
| [PC26]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC27}         | `PhysicalComplexity.AccessRegime.RegimeWithCertificateOn`                                              |
| [PC27]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC28}         | `PhysicalComplexity.AccessRegime.certificate_upgrades_regime_on`                                       |
| [PC28]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC29}         | `PhysicalComplexity.AccessRegime.regime_upgrade_with_certificate_on`                                   |
| [PC29]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC30}         | `PhysicalComplexity.coNP_not_in_P_physically`                                                          |
| [PC30]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC31}         | `PhysicalComplexity.pow2_eventually_exceeds`                                                           |
| [PC31]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PD2}          | `PhysicalDevice.is_succinct`                                                                           |
| [PD2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PD3}          | `PhysicalDevice.derived_explicit_size`                                                                 |
| [PD3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PD4}          | `PhysicalDevice.is_succinct_of_gap`                                                                    |
| [PD4]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PDS1}         | `ProductDistributionStructure.toDistribution`                                                          |
| [PDS1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PR1}          | `PolyReduction.comp_exists`                                                                            |
| [PR1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PR2}          | `PolyReduction.id`                                                                                     |
| [PR2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QA1}          | `QueryAlgorithm.run`                                                                                   |
| [QA1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QBF1}         | `QBF.eval`                                                                                             |
| [QBF1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QF1}          | `QFormula.eval`                                                                                        |
| [QF1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QF2}          | `QFormula.eval_map`                                                                                    |
| [QF2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QF3}          | `QFormula.map`                                                                                         |
| [QF3]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QT1}          | `QueryTranscript.size`                                                                                 |
| [QT1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:S1}           | `Signal.const`                                                                                         |
| [S1]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:S2}           | `Signal.priorOn`                                                                                       |
| [S2]{.sans-serif}      |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SAT3I1}       | `SAT3Instance.inputSize`                                                                               |
| [SAT3I1]{.sans-serif}  |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SCO1}         | `StochasticCriterionObjective.OptChance`                                                               |
| [SCO1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SCO2}         | `StochasticCriterionObjective.toExpectedDecisionProblem`                                               |
| [SCO2]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SDP1}         | `StochasticDecisionProblem.stochasticOpt`                                                              |
| [SDP1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SR1}          | `StaticRegime.toSequential`                                                                            |
| [SR1]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SR2}          | `StaticRegime.toStochastic`                                                                            |
| [SR2]{.sans-serif}     |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TCO1}         | `TransitionCoupledObjective.Opt`                                                                       |
| [TCO1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TCO2}         | `TransitionCoupledObjective.score`                                                                     |
| [TCO2]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TCO3}         | `TransitionCoupledObjective.toImmediateDecisionProblem`                                                |
| [TCO3]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TSO1}         | `TwoStepObjective.Opt`                                                                                 |
| [TSO1]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TSO2}         | `TwoStepObjective.score`                                                                               |
| [TSO2]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TSO3}         | `TwoStepObjective.toImmediateDecisionProblem`                                                          |
| [TSO3]{.sans-serif}    |                                                                                                        |
| :::                    |                                                                                                        |
+------------------------+--------------------------------------------------------------------------------------------------------+


## Assumption Ledger (Auto)

#### Source files.

-   `Paper4bStochasticSequential/ClaimClosure.lean`

#### Assumption bundles and fields.

-   (No assumption bundles parsed.)

#### Conditional closure handles.

-   (No conditional theorem handles parsed.)


  ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  **Paper handle**                              **Status**   **Lean support**
  --------------------------------------------- ------------ ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  `cor:exact-identifiability`                   Derived      `DQ.Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`

  `cor:exact-no-competence-zero-certified`      Full         `DQ.IntegrityCompetence.certificationOverheadBits_of_no_evidence`

  `cor:gap-externalization`                     Full         `DQ.HardnessDistribution.simplicityTax_grows`

  `cor:gap-minimization-hard`                   Derived      `DQ.Sigma2PHardness.min_representationGap_zero_iff_relevant_card`

  `cor:generalized-eventual-dominance`          Full         `DQ.HardnessDistribution.generalized_right_eventually_dominates_wrong`

  `cor:information-barrier-query`               Full         `DQ.ClaimClosure.exact_raw_eq_certified_iff_certainty_inflation_core`, `DQ.ClaimClosure.exact_raw_only_of_no_exact_admissible_core`, `DQ.ClaimClosure.explicit_assumptions_required_of_not_excused_core`

  `cor:integrity-universal`                     Full         `DQ.ClaimClosure.hard_family_all_coords_core`

  `cor:linear-positive-no-saturation`           Full         `DQ.HardnessDistribution.no_positive_slope_linear_represents_saturating`

  `cor:no-auto-minimize`                        Full         `DQ.ClaimClosure.horizonTwoWitness_immediate_empty_sufficient`

  `cor:no-uncertified-exact-claim`              Full         `DQ.ClaimClosure.information_barrier_value_entry_core`

  `cor:outside-excuses-no-exact-report`         Full         `DQ.ClaimClosure.information_barrier_opt_oracle_core`

  `cor:overmodel-diagnostic-implication`        Derived      `DQ.Sigma2PHardness.representationGap_eq_zero_iff`

  `cor:physics-no-universal-exact-claim`        Full         `DQ.ClaimClosure.horizon_gt_one_bridge_can_fail_on_sufficiency`

  `cor:practice-bounded`                        Full         `agentBridgeClass`

  `cor:practice-diagnostic`                     Derived      `DQ.Sigma2PHardness.min_representationGap_zero_iff_relevant_card`

  `cor:practice-structured`                     Full         `agent_transfer_licensed_iff_snapshot`

  `cor:practice-tree`                           Full         `anchor_sigma2p_complete_conditional`

  `cor:practice-unstructured`                   Full         `ExactPhysicalClaimWellTyped`

  `cor:query-obstruction-bool`                  Full         `DQ.ClaimClosure.no_auto_minimize_of_p_neq_conp`, `OneStepSequentialObjective`

  `cor:right-wrong-hardness`                    Full         `DQ.HardnessDistribution.right_dominates_wrong`

  `cor:type-system-threshold`                   Full         `DQ.HardnessDistribution.native_dominates_manual`

  `prop:abstention-frontier`                    Full         `DQ.ClaimClosure.no_exact_claim_under_declared_assumptions_unless_excused_core`

  `prop:adq-ordering`                           Full         `DQ.ClaimClosure.adq_ordering`

  `prop:attempted-competence-matrix`            Full         `DQ.IntegrityCompetence.EvidenceForReport`, `DQ.IntegrityCompetence.ExactCertaintyInflation`, `DQ.IntegrityCompetence.certaintyInflation_iff_not_admissible`

  `prop:bridge-failure-horizon`                 Full         `DQ.ClaimClosure.epsilon_admissible_iff_raw_lt_certified_total_core`, `DQ.ClaimClosure.exact_admissible_iff_raw_lt_certified_total_core`

  `prop:bridge-failure-stochastic`              Full         `DQ.ClaimClosure.selectorSufficient_not_implies_setSufficient`

  `prop:bridge-failure-transition`              Derived      `DQ.ClaimClosure.tractable_tree_core`

  `prop:bridge-transfer-scope`                  Full         `DQ.ClaimClosure.integrity_resource_bound_for_sufficiency`

  `prop:budgeted-crossover`                     Full         `DQ.ClaimClosure.meta_coordinate_not_relevant_on_declared_slice`, `DQ.PhysicalBudgetCrossover.explicit_infeasible_succinct_feasible_of_crossover`

  `prop:certified-confidence-gate`              Full         `DQ.IntegrityCompetence.certificationOverheadBits`, `DQ.IntegrityCompetence.certificationOverheadBits_of_evidence`

  `prop:crossover-above-cap`                    Full         `DQ.ClaimClosure.meta_coordinate_irrelevant_of_invariance_on_declared_slice`

  `prop:crossover-not-certification`            Full         `CC.lt`

  `prop:crossover-policy`                       Full         `DQ.ClaimClosure.minsuff_collapse_to_conp_conditional`

  `prop:declared-contract-selection-validity`   Full         `DQ.ClaimClosure.declaredRegimeFamily_complete`, `DQ.ClaimClosure.information_barrier_opt_oracle_core`

  `prop:dominance-modes`                        Full         `DQ.HardnessDistribution.centralized_higher_leverage`

  `prop:empty-sufficient-constant`              Full         `DQ.DecisionProblem.relevantSet_is_minimal`

  `prop:evidence-admissibility-equivalence`     Full         `DQ.IntegrityCompetence.ReportSignal`

  `prop:exact-requires-evidence`                Full         `DQ.IntegrityCompetence.ReportBitModel`, `DQ.IntegrityCompetence.SignalConsistent`

  `prop:generalized-assumption-boundary`        Full         `DQ.HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`, `DQ.HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`

  `prop:hardness-conservation`                  Full         `DQ.HardnessDistribution.totalDOF_ge_intrinsic`

  `prop:hardness-efficiency-interpretation`     Full         `DQ.HardnessDistribution.hardnessEfficiency_eq_central_share`

  `prop:heuristic-reusability`                  Full         `DQ.ClaimClosure.boundaryCharacterized_iff_exists_sufficient_subset`, `DQ.ClaimClosure.oracle_lattice_transfer_as_regime_simulation`, `DQ.ClaimClosure.physical_crossover_core`

  `prop:identifiability-convergence`            Full         `DQ.ClaimClosure.exact_certainty_inflation_under_hardness_core`

  `prop:insufficiency-counterexample`           Full         `DQ.ClaimClosure.DecisionProblem.sufficient_iff_zeroEpsilonSufficient`, `DQ.DecisionProblem.minimalSufficient_iff_relevant`

  `prop:integrity-competence-separation`        Full         `DQ.IntegrityCompetence.Percent`, `DQ.IntegrityCompetence.admissible_matrix_counts`

  `prop:integrity-resource-bound`               Full         `DQ.ClaimClosure.explicit_state_upper_core`, `DQ.IntegrityCompetence.abstain_signal_exists_with_guess_self`, `DQ.IntegrityCompetence.admissible_irrational_strictly_more_than_rational`

  `prop:mdp-tractable`                          Full         `DQ.ClaimClosure.query_obstruction_finite_state_core`

  `prop:minimal-relevant-equiv`                 Full         `DP.anchorSufficient`, `DQ.ClaimClosure.DecisionProblem.epsOpt_zero_eq_opt`

  `prop:no-evidence-zero-certified`             Full         `DQ.IntegrityCompetence.certifiedTotalBits`

  `prop:one-step-bridge`                        Full         `DQ.ClaimClosure.integrity_resource_bound_for_sufficiency`

  `prop:oracle-lattice-strict`                  Full         `ExcusedBy`, `ExplicitHardnessAssumptions`

  `prop:oracle-lattice-transfer`                Full         `DQ.ClaimClosure.integrity_universal_applicability_core`, `boundaryCharacterized`

  `prop:outside-excuses-explicit-assumptions`   Full         `DQ.ClaimClosure.declaredRegimeFamily_complete`

  `prop:physics-no-universal-exact`             Full         `DQ.ClaimClosure.cost_asymmetry_eth_conditional`

  `prop:query-finite-state-generalization`      Full         `RegimeSimulation`, `adq`

  `prop:query-randomized-robustness`            Full         `L.eval`, `TransitionCoupledObjective`, `TwoStepObjective`

  `prop:query-randomized-weighted`              Full         `bounded_actions_reusable_heuristic`, `bridgeFailureWitness`

  `prop:query-regime-obstruction`               Full         `DQ.ClaimClosure.no_exact_claim_admissible_under_hardness_core`, `RegimeSimulation`, `adq`

  `prop:query-state-batch-lb`                   Full         `StandardComplexityAssumptions`, `adq_ordering`

  `prop:query-subproblem-transfer`              Full         `DQ.ClaimClosure.one_step_bridge`, `DQ.ClaimClosure.sufficiency_conp_complete_conditional`, `DQ.ClaimClosure.sufficiency_conp_reduction_core`

  `prop:query-tightness-full-scan`              Full         `StructureDetectable`

  `prop:query-value-entry-lb`                   Full         `StochasticCriterionObjective`, `anchor_sigma2p_reduction_core`

  `prop:query-weighted-transfer`                Full         `boundaryCharacterized_iff_exists_sufficient_subset`, `bounded_actions_detectable`

  `prop:refinement-strengthens`                 Full         `DQ.ClaimClosure.thermo_mandatory_cost_core`

  `prop:retraction-evidence-integrity`          Full         `DQ.ClaimClosure.tractable_bounded_core`

  `prop:retraction-no-evidence-violates`        Full         `DQ.ClaimClosure.tractable_separable_core`

  `prop:selector-separation`                    Full         `DQ.ClaimClosure.physical_crossover_above_cap_core`

  `prop:sequential-bounded-horizon`             Full         `DQ.ClaimClosure.query_obstruction_boolean_corollary`

  `prop:sequential-static-relation`             Full         `DQ.ClaimClosure.physical_crossover_hardness_core`

  `prop:set-to-selector`                        Full         `DP.constant_opt_all_sufficient`

  `prop:snapshot-process-typing`                Full         `DQ.ClaimClosure.agent_transfer_licensed_iff_snapshot`, `DQ.ClaimClosure.minsuff_conp_complete_conditional`, `DQ.ClaimClosure.regime_core_claim_proved`

  `prop:static-stochastic-strict`               Unmapped     *(no derived Lean handle found)*

  `prop:static-stochastic-transfer`             Full         `DQ.ClaimClosure.regime_simulation_transfers_hardness`

  `prop:stochastic-bounded-support`             Full         `DQ.ClaimClosure.subproblem_hardness_lifts_to_full`

  `prop:stochastic-product-tractable`           Full         `DQ.ClaimClosure.subproblem_transfer_as_regime_simulation`

  `prop:stochastic-sequential-bridge-fail`      Full         `DQ.ClaimClosure.snapshot_vs_process_typed_boundary`

  `prop:stochastic-sequential-strict`           Unmapped     *(no derived Lean handle found)*

  `prop:sufficiency-char`                       Full         `DQ.ClaimClosure.thermo_energy_carbon_lift_core`, `DQ.ClaimClosure.thermo_eventual_lift_core`

  `prop:thermo-conservation-additive`           Full         `DQ.ClaimClosure.tractable_subcases_conditional`

  `prop:thermo-hardness-bundle`                 Full         `DQ.ClaimClosure.tree_structure_detectable`

  `prop:thermo-lift`                            Full         `DQ.ClaimClosure.tractable_tree_core`, `DQ.ClaimClosure.transition_coupled_bridge_can_fail_on_sufficiency`

  `prop:thermo-mandatory-cost`                  Full         `DQ.ClaimClosure.typed_claim_admissibility_core`

  `prop:typed-claim-admissibility`              Derived      `DQ.ClaimClosure.tree_structure_detectable`

  `prop:universal-solver-framing`               Derived      `DQ.ClaimClosure.typed_static_class_completeness`

  `prop:zero-epsilon-competence`                Full         `DQ.IntegrityCompetence.RLFFWeights`, `DQ.IntegrityCompetence.certifiedTotalBits_ge_raw`

  `prop:zero-epsilon-reduction`                 Full         `DP.classMonotoneOn`, `DQ.DecisionProblem.sufficient_implies_selectorSufficient`

  `thm:amortization`                            Full         `DQ.HardnessDistribution.complete_model_dominates_after_threshold`

  `thm:bridge-boundary-represented`             Full         `DQ.ClaimClosure.bounded_actions_detectable`, `DQ.ClaimClosure.bridge_boundary_represented_family`, `DQ.ClaimClosure.bridge_failure_witness_non_one_step`

  `thm:centralization-dominance`                Full         `DQ.HardnessDistribution.centralization_dominance_bundle`, `DQ.HardnessDistribution.centralization_step_saves_n_minus_one`

  `thm:claim-integrity-meta`                    Full         `DQ.ClaimClosure.declaredRegimeFamily_complete`

  `thm:config-reduction`                        Full         `DQ.ConfigReduction.config_sufficiency_iff_behavior_preserving`

  `thm:cost-asymmetry-eth`                      Full         `DQ.ClaimClosure.bridge_transfer_iff_one_step_class`, `DQ.HardnessDistribution.linear_lt_exponential_plus_constant_eventually`

  `thm:dichotomy`                               Full         `DQ.ClaimClosure.declaredBudgetSlice`, `DQ.ClaimClosure.declared_physics_no_universal_exact_certifier_core`, `DQ.ClaimClosure.dichotomy_conditional`

  `thm:generalized-dominance`                   Full         `DQ.HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`

  `thm:generalized-saturation-possible`         Full         `DQ.HardnessDistribution.generalizedTotal_with_saturation_eventually_constant`, `DQ.HardnessDistribution.saturatingSiteCost_eventually_constant`

  `thm:linear-saturation-iff-zero`              Full         `DQ.HardnessDistribution.totalDOF_eventually_constant_iff_zero_distributed`

  `thm:overmodel-diagnostic`                    Full         `DQ.ClaimClosure.anchor_sigma2p_reduction_core`, `DQ.ClaimClosure.information_barrier_state_batch_core`

  `thm:regime-coverage`                         Full         `DQ.ClaimClosure.certified_total_bits_split_core`, `DQ.ClaimClosure.no_exact_identifier_implies_not_boundary_characterized`

  `thm:tax-conservation`                        Full         `DQ.HardnessDistribution.gap_conservation_card`

  `thm:tax-grows`                               Derived      `DQ.HardnessDistribution.totalDOF_ge_intrinsic`

  `thm:tractable`                               Full         `DQ.ClaimClosure.universal_solver_framing_core`

  `thm:typed-completeness-static`               Derived      `DQ.ClaimClosure.typed_claim_admissibility_core`
  ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

*Notes:* *(1) Full rows come from theorem-local inline anchors in this paper.* *(2) Derived rows are filled by dependency/scaffold claim-handle derivation (same paper-handle label across proof dependencies).* *(3) Unmapped means no local anchor and no derivable dependency support were found.*

*Auto summary: mapped 100/102 (full=91, derived=9, unmapped=2).*




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper4_decision_quotient/proofs_4b/`
- Lines: 3288
- Theorems: 124
- `sorry` placeholders: 8
