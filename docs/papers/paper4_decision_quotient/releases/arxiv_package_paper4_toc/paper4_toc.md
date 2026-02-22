# Paper: Computational Complexity of Information Sufficiency

**Status**: Theory of Computing-ready | **Lean**: 8698 lines, 393 theorems

---

## Abstract

We characterize the computational complexity of *information sufficiency* as a *meta-problem*: given an arbitrary decision problem $\mathcal{D}$ with action set $A$, factored state space $S = X_1 \times \cdots \times X_n$, and utility $U: A \times S \to \mathbb{Q}$, does a candidate coordinate set $I$ carry enough information to act optimally? Formally, $I$ is *sufficient* if $s_I = s'_I \implies \operatorname{Opt}(s) = \operatorname{Opt}(s')$. Because the problems below are parameterized by an arbitrary $\mathcal{D}$, and any problem requiring a choice among alternatives under structured information instantiates the $(A, S, U)$ tuple, the complexity results apply to every problem with factored state space---not to a specific problem domain.

**The landscape in the formal model:**

-   **General case:** SUFFICIENCY-CHECK is coNP-complete; ANCHOR-SUFFICIENCY is $\Sigma_{2}^{P}$-complete.

-   **Tractable cases:** Polynomial-time for bounded action sets under the explicit-state encoding; separable utilities ($U = f + g$) under any encoding; and tree-structured utility with explicit local factors.

-   **Encoding-regime separation:** Polynomial-time under the explicit-state encoding (polynomial in $|S|$). Under ETH, there exist succinctly encoded worst-case instances witnessed by a strengthened gadget construction (mechanized in Lean; see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}) with $k^*=n$ for which SUFFICIENCY-CHECK requires $2^{\Omega(n)}$ time.

-   **Intermediate query-access lower bounds:** In the finite-state query core, SUFFICIENCY-CHECK has worst-case Opt-oracle query complexity $\Omega(|S|)$ via indistinguishable yes/no pairs for the $I=\emptyset$ subproblem (Boolean instantiation: $\Omega(2^n)$); mechanized Boolean interface refinements show the same obstruction for value-entry and state-batch access, including finite-support randomized robustness and oracle-lattice transfer/strictness statements.

The tractable cases are stated with explicit encoding assumptions (Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}). Together, these results answer the question "when is decision-relevant information identifiable efficiently?" within the stated regimes. Complexity classification is a property of the encoding regime measured against a fixed decision question (Remark [\[rem:question-vs-problem\]](#rem:question-vs-problem){reference-type="ref" reference="rem:question-vs-problem"}): the same sufficiency predicate is polynomial-time under explicit-state access and worst-case exponential under succinct encoding. At the structural level, the apparent $\exists\forall$ form of MINIMUM-SUFFICIENT-SET collapses to a coNP characterization via the criterion $\text{sufficient}(I) \iff \text{Relevant} \subseteq I$. Within this regime-typed framework, over-modeling is rational only under integrity-preserving attempted-competence-failure conditions; otherwise it is irrational. \[D:prop:attempted-competence-matrix; R:\[R=active declared regime\]\]

The contribution has two levels: (i) a complete complexity landscape for the core decision-relevant problems in the static sufficiency class defined by the model contract (coNP/$\Sigma_2^P$ completeness and tractable regimes under explicit encoding assumptions), and (ii) a formal regime-typing framework that separates structural complexity from representational hardness and yields theorem-indexed engineering corollaries.

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 (8698 lines, 393 theorem/lemma statements); complexity classifications follow by composition with standard results (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}).

**Keywords:** computational complexity, decision theory, polynomial hierarchy, tractability dichotomy, Lean 4


# Introduction {#sec:introduction}

Consider any decision problem $\mathcal{D}$ with actions $A$ and factored state space $S = X_1 \times \cdots \times X_n$. A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only coordinates in $I$ determines the optimal action: $$s_I = s'_I \implies \operatorname{Opt}(s) = \operatorname{Opt}(s')$$ This is *coordinate sufficiency*---the formalization of *information sufficiency* (whether available information determines the optimal action) over a factored state space.

SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, and ANCHOR-SUFFICIENCY are *meta-problems*: each is parameterized by an arbitrary decision problem $\mathcal{D}$ and asks a structural question about $\mathcal{D}$'s coordinate space. The complexity results therefore apply to every problem with factored state space, not to a specific problem domain. \[D:thm:sufficiency-conp, thm:minsuff-conp, thm:anchor-sigma2p; R:\[S\]\]

::: remark
[]{#rem:universality label="rem:universality"} The formal object of this paper is the decision-problem tuple $\mathcal{D} = (A, S, U)$: actions, factored states, utility. This is not a restriction. Any problem requiring a choice among alternatives given structured information instantiates the tuple: the alternatives are $A$, the structured information is $S = X_1 \times \cdots \times X_n$, and the objective is $U$. "Decision problem" is therefore coextensive with "problem"---the qualifier restricts nothing. The meta-problem results below are universal over all problems with coordinate structure; the $(A, S, U)$ formalism provides the coordinate framework for stating the sufficiency predicate, not a boundary on the class of problems to which the results apply.
:::

This paper characterizes the complexity landscape of these meta-problems within the formal model:

Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"} fixes the computational model and input encodings used for all complexity claims. Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"} gives the model contract and regime tags used to type every strong claim. Completeness claims are class-internal: complete for the static sufficiency class fixed by C1--C4 and the declared access regimes. Adjacent objective classes that violate the bridge conditions are typed separately (Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"}).

::: center
  **Problem**              **Complexity**              **When Tractable**
  ------------------------ --------------------------- ------------------------------------------------------------------------------
  SUFFICIENCY-CHECK        coNP-complete               Bounded actions (explicit-state), separable utility, tree-structured utility
  MINIMUM-SUFFICIENT-SET   coNP-complete               Same conditions
  ANCHOR-SUFFICIENCY       $\Sigma_{2}^{P}$-complete   Open
:::

The tractable cases are stated with explicit encoding assumptions (Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}). Outside those regimes, the succinct model yields hardness.

## Hardness--Recovery Reading Map

Theorems in this paper are intended to be read as hardness/recovery pairs for the same fixed decision question:

1.  **Sufficiency checking:** \[S\] coNP-complete in the general succinct regime (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), paired with polynomial-time recovery under explicit-state and structured-access regimes (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

2.  **Minimal sufficient sets:** \[S\] coNP-complete in general (Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}), paired with the collapse criterion and relevance-computation recovery route (Theorems [\[thm:minsuff-collapse\]](#thm:minsuff-collapse){reference-type="ref" reference="thm:minsuff-collapse"}, [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

3.  **Anchor sufficiency:** $\Sigma_{2}^{P}$-complete in the general anchored formulation (Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"}); no general polynomial-time recovery condition is established in this model.

An operational criterion follows later from the same chain: once decision-site count exceeds the amortization threshold $n^*$, avoiding structural identification is more expensive than paying the one-time centralization cost (Theorem [\[thm:amortization\]](#thm:amortization){reference-type="ref" reference="thm:amortization"}).

## Landscape Summary

**When is sufficiency checking tractable?** We identify three sufficient conditions:

1.  **Bounded actions** ($|A| \leq k$) under explicit-state encoding: with constantly many actions, we enumerate action pairs over the explicit utility table.

2.  **Separable utility** ($U(a,s) = f(a) + g(s)$): The optimal action depends only on $f$, making all coordinates irrelevant to the decision.

3.  **Tree-structured utility**: With explicit local factors over a tree, dynamic programming yields polynomial algorithms in the input length.

Each condition is stated with its encoding assumption. Outside these regimes, the general problem remains coNP-hard (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}).

**When is it intractable?** The general problem is coNP-complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), with a separation between explicit-state tractability and succinct worst-case hardness:

-   In the explicit-state model: SUFFICIENCY-CHECK is solvable in polynomial time in $|S|$ by explicitly computing $\operatorname{Opt}(s)$ for all $s\in S$ and checking all pairs $(s,s')$ with equal $I$-projection. In particular, instances with $k^* = O(\log |S|)$ are tractable in this model.

-   In the intermediate query-access model: the finite-state core yields an Opt-oracle lower bound $\Omega(|S|)$ (Boolean instantiation: $\Omega(2^n)$), and the mechanized Boolean interface refinements preserve the obstruction for value-entry and state-batch interfaces, with explicit subproblem-to-full transfer, weighted randomized robustness, and oracle-lattice transfer/strictness theorems (Propositions [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"}--[\[prop:oracle-lattice-strict\]](#prop:oracle-lattice-strict){reference-type="ref" reference="prop:oracle-lattice-strict"}).

-   In the succinct model: under ETH there exist worst-case instances produced by our strengthened gadget in which the minimal sufficient set has size $\Omega(n)$ (indeed $n$) and SUFFICIENCY-CHECK requires $2^{\Omega(n)}$ time.

The explicit ETH lower bound is still a succinct worst-case statement; Proposition [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"} provides the finite-state query core and Propositions [\[prop:query-value-entry-lb\]](#prop:query-value-entry-lb){reference-type="ref" reference="prop:query-value-entry-lb"}--[\[prop:oracle-lattice-strict\]](#prop:oracle-lattice-strict){reference-type="ref" reference="prop:oracle-lattice-strict"} provide theorem-level Boolean-interface refinements.

## Main Theorems

1.  **Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}:** SUFFICIENCY-CHECK is coNP-complete via reduction from TAUTOLOGY.

2.  **Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}:** MINIMUM-SUFFICIENT-SET is coNP-complete (the $\Sigma_{2}^{P}$ structure collapses).

3.  **Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"}:** ANCHOR-SUFFICIENCY is $\Sigma_{2}^{P}$-complete via reduction from $\exists\forall$-SAT.

4.  **Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}:** Encoding-regime separation: explicit-state polynomial-time (polynomial in $|S|$), and under ETH a succinct worst-case lower bound witnessed by a hard family with $k^* = n$.

5.  **Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}:** Polynomial algorithms for bounded actions, separable utility, tree structure.

## Machine-Checked Proofs

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 [@moura2021lean4] (8698 lines, 393 theorem/lemma statements). The formalization verifies that the TAUTOLOGY reduction correctly maps tautologies to sufficient coordinate sets. Complexity class membership (coNP-completeness, $\Sigma_2^P$-completeness) follows by composition with standard complexity-theoretic results.

#### What is new.

We contribute (i) formal definitions of decision-theoretic sufficiency in Lean; (ii) machine-checked proofs of reduction correctness for the TAUTOLOGY and $\exists\forall$-SAT reductions; (iii) a complete complexity landscape for coordinate sufficiency with explicit encoding assumptions; and (iv) a formal separation between structural complexity and representational hardness used to derive theorem-indexed engineering corollaries, including theorem-level typed coverage/completeness closures for the declared static class (Theorems [\[thm:regime-coverage\]](#thm:regime-coverage){reference-type="ref" reference="thm:regime-coverage"}, [\[thm:typed-completeness-static\]](#thm:typed-completeness-static){reference-type="ref" reference="thm:typed-completeness-static"}). Prior work establishes hardness informally; we formalize the constructions and their regime-typed consequences.

## Paper Structure

The primary contribution is theoretical: a formalized reduction framework and a complete characterization of the core decision-relevant problems in the formal model (coNP/$\Sigma_2^P$ completeness and tractable cases stated under explicit encoding assumptions). A second contribution is formal claim typing: Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"} introduces the structural/representational and integrity/competence splits that type-check the applied corollaries.

Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"}: decision-problem foundations and encoding model. Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"}: structural vs representational hardness; integrity vs competence. Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}: hardness proofs. Section [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"}: regime separation. Section [\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"}: tractable cases. Section [\[sec:engineering-justification\]](#sec:engineering-justification){reference-type="ref" reference="sec:engineering-justification"}: regime-conditional corollaries. Section [\[sec:implications\]](#sec:implications){reference-type="ref" reference="sec:implications"}: dominance theorems for hardness placement. Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"}: conservation law for decision-relevant coordinates. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"}: related work. Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}: Lean listings.

Sections [\[sec:engineering-justification\]](#sec:engineering-justification){reference-type="ref" reference="sec:engineering-justification"}--[\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} are not applied commentary. Every claim in those sections is a formal corollary, regime-typed by the framework of Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"} and indexed to a machine-checked theorem handle. They complete the complexity landscape by characterizing when exact minimization is rational and when it is not: the rationality matrix (Proposition [\[prop:attempted-competence-matrix\]](#prop:attempted-competence-matrix){reference-type="ref" reference="prop:attempted-competence-matrix"}), the dominance and conservation theorems (Theorems [\[thm:centralization-dominance\]](#thm:centralization-dominance){reference-type="ref" reference="thm:centralization-dominance"}, [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"}), and the amortization threshold (Theorem [\[thm:amortization\]](#thm:amortization){reference-type="ref" reference="thm:amortization"}) are all mechanized in Lean.


# Formal Foundations {#sec:foundations}

We formalize decision problems with coordinate structure, sufficiency of coordinate sets, and the decision quotient, drawing on classical decision theory [@savage1954foundations; @raiffa1961applied].

## Decision Problems with Coordinate Structure

::: definition
[]{#def:decision-problem label="def:decision-problem"} A *decision problem with coordinate structure* is a tuple $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ where:

-   $A$ is a finite set of *actions* (alternatives)

-   $X_1, \ldots, X_n$ are finite *coordinate spaces*

-   $S = X_1 \times \cdots \times X_n$ is the *state space*

-   $U : A \times S \to \mathbb{Q}$ is the *utility function*
:::

::: definition
[]{#def:projection label="def:projection"} For state $s = (s_1, \ldots, s_n) \in S$ and coordinate set $I \subseteq \{1, \ldots, n\}$: $$s_I := (s_i)_{i \in I}$$ is the *projection* of $s$ onto coordinates in $I$.
:::

::: definition
[]{#def:optimizer label="def:optimizer"} For state $s \in S$, the *optimal action set* is: $$\operatorname{Opt}(s) := \arg\max_{a \in A} U(a, s) = \{a \in A : U(a,s) = \max_{a' \in A} U(a', s)\}$$
:::

## Sufficiency and Relevance

::: definition
[]{#def:sufficient label="def:sufficient"} A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* for decision problem $\mathcal{D}$ if: $$\forall s, s' \in S: \quad s_I = s'_I \implies \operatorname{Opt}(s) = \operatorname{Opt}(s')$$ Equivalently, the optimal action depends only on coordinates in $I$. In this paper, this set-valued invariance of the full optimal-action correspondence is the primary decision-relevance target.
:::

::: definition
[]{#def:selector label="def:selector"} A *deterministic selector* is a map $\sigma : 2^A \to A$ that returns one action from an optimal-action set.
:::

::: definition
[]{#def:selector-sufficient label="def:selector-sufficient"} For fixed selector $\sigma$, a coordinate set $I$ is *selector-sufficient* if $$\forall s,s' \in S:\quad s_I=s'_I \implies \sigma(\operatorname{Opt}(s))=\sigma(\operatorname{Opt}(s')).$$
:::

::: proposition
[]{#prop:set-to-selector label="prop:set-to-selector"} If $I$ is sufficient in the set-valued sense (Definition [\[def:sufficient\]](#def:sufficient){reference-type="ref" reference="def:sufficient"}), then $I$ is selector-sufficient for every deterministic selector $\sigma$ (Definition [\[def:selector-sufficient\]](#def:selector-sufficient){reference-type="ref" reference="def:selector-sufficient"}).
:::

::: proof
*Proof.* If $I$ is sufficient, then $s_I=s'_I$ implies $\operatorname{Opt}(s)=\operatorname{Opt}(s')$. Applying any deterministic selector $\sigma$ to equal optimal-action sets yields equal selected actions. ◻
:::

::: definition
[]{#def:epsilon-sufficiency label="def:epsilon-sufficiency"} For $\varepsilon \ge 0$, define $$\operatorname{Opt}_\varepsilon(s)
:=
\{a\in A:\forall a'\in A,\ U(a',s)\le U(a,s)+\varepsilon\}.$$ Coordinate set $I$ is *$\varepsilon$-sufficient* if $$\forall s,s'\in S:\ s_I=s'_I \implies \operatorname{Opt}_\varepsilon(s)=\operatorname{Opt}_\varepsilon(s').$$
:::

::: proposition
[]{#prop:zero-epsilon-reduction label="prop:zero-epsilon-reduction"} Set-valued sufficiency is exactly the $\varepsilon=0$ case: $$I\text{ sufficient } \iff I\text{ is }0\text{-sufficient}.$$
:::

::: proposition
[]{#prop:selector-separation label="prop:selector-separation"} The converse of Proposition [\[prop:set-to-selector\]](#prop:set-to-selector){reference-type="ref" reference="prop:set-to-selector"} fails in general: there exists a decision problem, selector, and coordinate set $I$ such that $I$ is selector-sufficient but not sufficient in the full set-valued sense.
:::

::: definition
[]{#def:minimal-sufficient label="def:minimal-sufficient"} A sufficient set $I$ is *minimal* if no proper subset $I' \subsetneq I$ is sufficient.
:::

::: definition
[]{#def:relevant label="def:relevant"} Coordinate $i$ is *relevant* if there exist states that differ only at coordinate $i$ and induce different optimal action sets: $$i \text{ is relevant}
\iff
\exists s,s' \in S:\; \Big(\forall j \neq i,\; s_j = s'_j\Big)\ \wedge\ \operatorname{Opt}(s)\neq\operatorname{Opt}(s').$$
:::

::: proposition
[]{#prop:minimal-relevant-equiv label="prop:minimal-relevant-equiv"} For any minimal sufficient set $I$ and any coordinate $i$: $$i \in I \iff i \text{ is relevant}.$$ Hence every minimal sufficient set is exactly the relevant-coordinate set.
:::

::: proof
*Proof.* The "only if" direction follows by minimality: if $i\in I$ were irrelevant, removing $i$ would preserve sufficiency, contradicting minimality. The "if" direction follows from sufficiency: every sufficient set must contain each relevant coordinate. ◻
:::

::: definition
[]{#def:exact-identifiability label="def:exact-identifiability"} For a decision problem $\mathcal{D}$ and candidate coordinate set $I$, we say $I$ is *exactly relevance-identifying* if $$\forall i \in \{1,\ldots,n\}:\quad i \in I \iff i \text{ is relevant for } \mathcal{D}.$$ Equivalently, $I$ is exactly relevance-identifying iff $I$ equals the full relevant-coordinate set.
:::

::: example
Consider deciding whether to carry an umbrella:

-   Actions: $A = \{\text{carry}, \text{don't carry}\}$

-   Coordinates: $X_1 = \{\text{rain}, \text{no rain}\}$, $X_2 = \{\text{hot}, \text{cold}\}$, $X_3 = \{\text{Monday}, \ldots, \text{Sunday}\}$

-   Utility: $U(\text{carry}, s) = -1 + 3 \cdot \mathbf{1}[s_1 = \text{rain}]$, $U(\text{don't carry}, s) = -2 \cdot \mathbf{1}[s_1 = \text{rain}]$

The minimal sufficient set is $I = \{1\}$ (only rain forecast matters). Coordinates 2 and 3 (temperature, day of week) are irrelevant.
:::

## The Decision Quotient

::: definition
[]{#def:decision-equiv label="def:decision-equiv"} For coordinate set $I$, states $s, s'$ are *$I$-equivalent* (written $s \sim_I s'$) if $s_I = s'_I$.
:::

::: definition
[]{#def:decision-quotient label="def:decision-quotient"} The *decision quotient* for state $s$ under coordinate set $I$ is: $$\text{DQ}_I(s) = \frac{|\{a \in A : a \in \operatorname{Opt}(s') \text{ for some } s' \sim_I s\}|}{|A|}$$ This measures the fraction of actions that are optimal for at least one state consistent with $I$.
:::

::: proposition
[]{#prop:sufficiency-char label="prop:sufficiency-char"} Coordinate set $I$ is sufficient if and only if $\text{DQ}_I(s) = |\operatorname{Opt}(s)|/|A|$ for all $s \in S$.
:::

::: proof
*Proof.* If $I$ is sufficient, then $s \sim_I s' \implies \operatorname{Opt}(s) = \operatorname{Opt}(s')$, so the set of actions optimal for some $s' \sim_I s$ is exactly $\operatorname{Opt}(s)$.

Conversely, if the condition holds, then for any $s \sim_I s'$, the optimal actions form the same set (since $\text{DQ}_I(s) = \text{DQ}_I(s')$ and both equal the relative size of the common optimal set). ◻
:::

## Computational Model and Input Encoding {#sec:encoding}

We fix the computational model used by the complexity claims.

#### Succinct encoding (primary for hardness).

This succinct circuit encoding is the standard representation for decision problems in complexity theory; hardness is stated with respect to the input length of the circuit description [@arora2009computational]. An instance is encoded as:

-   a finite action set $A$ given explicitly,

-   coordinate domains $X_1,\ldots,X_n$ given by their sizes in binary,

-   a Boolean or arithmetic circuit $C_U$ that on input $(a,s)$ outputs $U(a,s)$.

The input length is $L = |A| + \sum_i \log |X_i| + |C_U|$. Polynomial time and all complexity classes (coNP, $\Sigma_2^P$, ETH) are measured in $L$. All hardness results in Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} use this encoding.

#### Explicit-state encoding (used for enumeration algorithms and experiments).

The utility is given as a full table over $A \times S$. The input length is $L_{\text{exp}} = \Theta(|A||S|)$ (up to the bitlength of utilities). Polynomial time is measured in $L_{\text{exp}}$. Results stated in terms of $|S|$ use this encoding.

#### Query-access regime (intermediate black-box access).

The solver is given oracle access to decision information at queried states (e.g., $\operatorname{Opt}(s)$, or $U(a,s)$ with $\operatorname{Opt}(s)$ reconstructed from finitely many value queries). Complexity is measured by oracle-query count (optionally paired with per-query evaluation cost). This separates representational access from full-table availability and from succinct-circuit input length.

Unless explicitly stated otherwise, "polynomial time" refers to the succinct encoding.

::: remark
[]{#rem:question-vs-problem label="rem:question-vs-problem"} We distinguish between a *decision question* and a *decision problem*. A decision question is the encoding-independent predicate: "is coordinate set $I$ sufficient for $\mathcal{D}$?" This is a mathematical relation, fixed by the model contract (C1--C4). A decision problem is a decision question together with a specific encoding of its inputs. The same decision question yields different decision problems under different encodings, and these problems may belong to different complexity classes. Formally, each encoding regime $e$ induces a language $L_{\mathcal{D},e}$; complexity classification is a property of $L_{\mathcal{D},e}$, not of $\mathcal{D}$ alone.
:::

::: definition
[]{#def:regime-simulation label="def:regime-simulation"} Fix a decision question $Q$ and two regimes $R_1,R_2$ for that question. We say $R_1$ *simulates* $R_2$ if there exists a polynomial-time transformer that maps any $R_2$ instance to an $R_1$ instance while preserving the answer to $Q$; in oracle settings, this includes a polynomial-time transcript transducer that preserves yes/no outcomes for induced solvers.
:::

This paper uses that simulation spine in two explicit forms: restriction-map simulation (subproblem-to-full transfer; Proposition [\[prop:query-subproblem-transfer\]](#prop:query-subproblem-transfer){reference-type="ref" reference="prop:query-subproblem-transfer"}) and oracle-transducer simulation (batch-to-entry transfer; Proposition [\[prop:oracle-lattice-transfer\]](#prop:oracle-lattice-transfer){reference-type="ref" reference="prop:oracle-lattice-transfer"}).

## Model Contract and Regime Tags {#sec:model-contract}

All theorem statements in this paper are typed by the following model contract:

-   **C1 (finite actions):** $A$ is finite.

-   **C2 (finite coordinate domains):** each $X_i$ is finite, so $S=\prod_i X_i$ is finite.

-   **C3 (evaluable utility):** $U(a,s)$ is computable from the declared input encoding.

-   **C4 (fixed decision semantics):** optimality is defined by $\operatorname{Opt}(s)=\arg\max_a U(a,s)$.

We use short regime tags for applied corollaries:

-   **\[E\]** explicit-state encoding,

-   **\[Q\]** query-access (oracle) regime,

-   **\[Q_fin\]** finite-state query-access core (state-oracle),

-   **\[S\]** succinct encoding,

-   **\[S+ETH\]** succinct encoding with ETH,

-   **\[Q_bool\]** mechanized Boolean query submodel,

-   **\[S_bool\]** mechanized Boolean-coordinate submodel.

This tagging is a claim-typing convention: each strong statement is attached to the regime where it is proven.

::: theorem
[]{#thm:regime-coverage label="thm:regime-coverage"} Let $$\mathcal{R}_{\mathrm{static}} =
\{\text{[E]},\ \text{[S+ETH]},\ \text{[Q\_fin:Opt]},\ \text{[Q\_bool:value-entry]},\ \text{[Q\_bool:state-batch]}\}.$$ For each declared regime in $\mathcal{R}_{\mathrm{static}}$, the paper has a theorem-level mechanized core claim. Equivalently, regime typing is complete over the declared static family.
:::

#### Scope Lattice (typed classes and transfer boundary).

::: center
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  **Layer**                                                                               **Transfer Status**           **Lean handles (representative)**
  --------------------------------------------------------------------------------------- ----------------------------- ----------------------------------------------------
  Static sufficiency class (C1--C4; declared regimes)                                     Internal landscape complete   `ClaimClosure.typed_static_class_completeness`

  `ClaimClosure.regime_core_claim_proved`                                                                               

  Bridge-admissible adjacent class (one-step deterministic)                               Transfer licensed             `ClaimClosure.one_step_bridge`

  `ClaimClosure.bridge_transfer_iff_one_step_class`                                                                     

  Non-admissible represented adjacent classes (horizon, stochastic, transition-coupled)   Transfer blocked by witness   `ClaimClosure.bridge_failure_witness_non_one_step`

  `ClaimClosure.bridge_boundary_represented_family`                                                                     
  --------------------------------------------------------------------------------------------------------------------------------------------------------------------------
:::

## Adjacent Objective Regimes and Bridge

::: definition
[]{#def:adjacent-sequential-regime label="def:adjacent-sequential-regime"} An adjacent sequential objective instance consists of:

-   finite action set $A$,

-   finite coordinate state space $S = X_1 \times \cdots \times X_n$,

-   horizon $T \in \mathbb{N}_{\ge 1}$ and history-dependent policy class,

-   reward process $r_t$ and objective functional $J(\pi)$ (e.g., cumulative reward or regret).
:::

::: proposition
[]{#prop:one-step-bridge label="prop:one-step-bridge"} Consider an instance of Definition [\[def:adjacent-sequential-regime\]](#def:adjacent-sequential-regime){reference-type="ref" reference="def:adjacent-sequential-regime"} satisfying:

1.  $T=1$,

2.  deterministic rewards $r_1(a,s)=U(a,s)$ for some evaluable $U$,

3.  objective $J(\pi)=U(\pi(s),s)$ (single-step maximization),

4.  no post-decision state update relevant to the objective.

Then the induced optimization problem is exactly the static decision problem of Definition [\[def:decision-problem\]](#def:decision-problem){reference-type="ref" reference="def:decision-problem"}, and coordinate sufficiency in the sequential formulation is equivalent to Definition [\[def:sufficient\]](#def:sufficient){reference-type="ref" reference="def:sufficient"}.
:::

::: proof
*Proof.* Under (1)--(3), optimizing $J$ at state $s$ is identical to choosing an action in $\arg\max_{a\in A} U(a,s)=\operatorname{Opt}(s)$. Condition (4) removes any dependence on future transition effects. Therefore the optimal-policy relation in the adjacent formulation coincides pointwise with $\operatorname{Opt}$ from Definition [\[def:optimizer\]](#def:optimizer){reference-type="ref" reference="def:optimizer"}, and the invariance condition "same projection implies same optimal choice set" is exactly Definition [\[def:sufficient\]](#def:sufficient){reference-type="ref" reference="def:sufficient"}. ◻
:::

::: proposition
[]{#prop:bridge-transfer-scope label="prop:bridge-transfer-scope"} Under conditions (1)--(4), any sufficiency statement formulated over Definition [\[def:sufficient\]](#def:sufficient){reference-type="ref" reference="def:sufficient"} is equivalent between the adjacent sequential formulation and the static model.
:::

::: proof
*Proof.* By Proposition [\[prop:one-step-bridge\]](#prop:one-step-bridge){reference-type="ref" reference="prop:one-step-bridge"}, the adjacent sequential objective induces exactly the same sufficiency predicate as Definition [\[def:sufficient\]](#def:sufficient){reference-type="ref" reference="def:sufficient"} when (1)--(4) hold. Equivalence of any sufficiency statement then follows by substitution. ◻
:::

If any bridge condition fails, direct transfer from this paper's static complexity theorems is not licensed by this rule.

::: remark
Beyond Proposition [\[prop:one-step-bridge\]](#prop:one-step-bridge){reference-type="ref" reference="prop:one-step-bridge"} (multi-step horizon, stochastic transitions/rewards, or regret objectives), the governing complexity objects change. Those regimes are natural extensions, but they are distinct formal classes from the static sufficiency class analyzed in this paper.
:::

::: proposition
[]{#prop:bridge-failure-horizon label="prop:bridge-failure-horizon"} Dropping the one-step condition can break sufficiency transfer: there exists a two-step objective where sufficiency in the immediate-utility static projection does not match sufficiency in the two-step objective.
:::

::: proposition
[]{#prop:bridge-failure-stochastic label="prop:bridge-failure-stochastic"} If optimization is performed against a stochastic criterion not equal to deterministic utility maximization, bridge transfer to Definition [\[def:decision-problem\]](#def:decision-problem){reference-type="ref" reference="def:decision-problem"} can fail even when an expected-utility projection is available.
:::

::: proposition
[]{#prop:bridge-failure-transition label="prop:bridge-failure-transition"} If post-decision transition effects are objective-relevant, bridge transfer to the static one-step class can fail.
:::

::: theorem
[]{#thm:bridge-boundary-represented label="thm:bridge-boundary-represented"} Within the represented adjacent family $$\{\text{one-step deterministic},\ \text{horizon-extended},\ \text{stochastic-criterion},\ \text{transition-coupled}\},$$ direct transfer of static sufficiency claims is licensed if and only if the class is one-step deterministic. Each represented non-one-step class has an explicit mechanized bridge-failure witness.
:::

::: definition
[]{#def:agent-snapshot-process label="def:agent-snapshot-process"} Within the represented adjacent family, we type:

-   *agent snapshot*: fixed-parameter inference view (mapped to one-step deterministic class),

-   *agent process*: online/dynamical update views (horizon-extended, stochastic-criterion, or transition-coupled classes).
:::

::: proposition
[]{#prop:snapshot-process-typing label="prop:snapshot-process-typing"} In the represented adjacent family, direct transfer of static sufficiency claims is licensed if and only if the agent is typed as an *agent snapshot*. Every process-typed represented class has an explicit mechanized bridge-failure witness.
:::

Operationally: a trained model evaluated with fixed parameters during inference is an agent snapshot for this typing; once parameters or transition-relevant internals are updated online, the object is process-typed and transfer from static sufficiency theorems is blocked unless the one-step bridge conditions are re-established. \[D:prop:snapshot-process-typing; R:\[R=represented adjacent class\]\]

# Interpretive Foundations: Hardness and Solver Claims {#sec:interpretive-foundations}

The claims in later applied sections are theorem-indexed consequences of this section and Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}--[\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"}.

## Structural Complexity vs Representational Hardness

::: definition
[]{#def:structural-complexity label="def:structural-complexity"} For a fixed decision question (e.g., "is $I$ sufficient for $\mathcal{D}$?"; see Remark [\[rem:question-vs-problem\]](#rem:question-vs-problem){reference-type="ref" reference="rem:question-vs-problem"}), *structural complexity* means its placement in standard complexity classes within the formal model (coNP, $\Sigma_2^P$, etc.), as established by class-membership arguments and reductions.
:::

::: definition
[]{#def:representational-hardness label="def:representational-hardness"} For a fixed decision question and an encoding regime $E$ (Section [1.4](#sec:encoding){reference-type="ref" reference="sec:encoding"}), *representational hardness* is the worst-case computational cost incurred by solvers whose input access is restricted to $E$.
:::

::: remark
This paper keeps the decision question fixed and varies the encoding regime explicitly. Thus, later separations are read as changes in representational hardness under fixed structural complexity, not as changes to the underlying sufficiency semantics. Accordingly, "complete landscape" means complete for this static sufficiency class under the declared regimes; adjacent objective classes are distinct typed objects, not unproved remainder cases of the same class.
:::

::: theorem
[]{#thm:typed-completeness-static label="thm:typed-completeness-static"} For the static sufficiency class fixed by C1--C4 and declared regime family $\mathcal{R}_{\mathrm{static}}$, the paper provides:

1.  conditional class-label closures for SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, and ANCHOR-SUFFICIENCY;

2.  a conditional explicit/succinct dichotomy closure;

3.  a regime-indexed mechanized core claim for every declared regime; and

4.  declared-family exhaustiveness in the typed regime algebra.
:::

## Solver Integrity and Regime Competence

To keep practical corollaries type-safe, we separate *integrity* (what a solver is allowed to assert) from *competence* (what it can cover under a declared regime), following the certifying-algorithms schema [@mcconnell2010certifying].

::: definition
[]{#def:certifying-solver label="def:certifying-solver"} Fix a decision question $\mathcal{R} \subseteq \mathcal{X}\times\mathcal{Y}$ and an encoding regime $E$ over $\mathcal{X}$. A *certifying solver* is a pair $(Q,V)$ where:

-   $Q$ maps each input $x\in\mathcal{X}$ to either $\mathsf{ABSTAIN}$ or a candidate pair $(y,w)$,

-   $V$ is a polynomial-time checker (in $|{\rm enc}_E(x)|$) with output in $\{0,1\}$.
:::

::: definition
[]{#def:solver-integrity label="def:solver-integrity"} A certifying solver $(Q,V)$ has *integrity* for relation $\mathcal{R}$ if:

-   (assertion soundness) $Q(x)=(y,w)\implies V(x,y,w)=1$,

-   (checker soundness) $V(x,y,w)=1\implies (x,y)\in\mathcal{R}$.

The output $\mathsf{ABSTAIN}$ (equivalently, $\mathsf{UNKNOWN}$) is first-class and carries no assertion about membership in $\mathcal{R}$.
:::

::: definition
[]{#def:competence-regime label="def:competence-regime"} Fix a regime $\Gamma=(\mathcal{X}_\Gamma,E_\Gamma,\mathcal{C}_\Gamma)$ with instance family $\mathcal{X}_\Gamma\subseteq\mathcal{X}$, encoding assumptions $E_\Gamma$, and resource bound $\mathcal{C}_\Gamma$. A certifying solver $(Q,V)$ is *competent* on $\Gamma$ for relation $\mathcal{R}$ if:

-   it has integrity for $\mathcal{R}$ (Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"}),

-   (coverage) $\forall x\in\mathcal{X}_\Gamma,\;Q(x)\neq\mathsf{ABSTAIN}$,

-   (resource bound) runtime$_Q(x)\le \mathcal{C}_\Gamma(|{\rm enc}_{E_\Gamma}(x)|)$ for all $x\in\mathcal{X}_\Gamma$.
:::

::: definition
[]{#def:epsilon-objective-family label="def:epsilon-objective-family"} An *$\varepsilon$-objective relation family* is a map $$\varepsilon \mapsto \mathcal{R}_\varepsilon \subseteq \mathcal{X}\times\mathcal{Y}$$ that assigns a certified target relation to each tolerance level $\varepsilon\ge 0$. The exact target is $\mathcal{R}_0$.
:::

::: definition
[]{#def:epsilon-competence-regime label="def:epsilon-competence-regime"} Fix a relation family $(\mathcal{R}_\varepsilon)_{\varepsilon\ge 0}$ and regime $\Gamma$. A certifying solver $(Q,V)$ is *$\varepsilon$-competent* on $\Gamma$ if it is competent on $\Gamma$ for relation $\mathcal{R}_\varepsilon$ in the sense of Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}.
:::

::: proposition
[]{#prop:zero-epsilon-competence label="prop:zero-epsilon-competence"} If $\mathcal{R}_0=\mathcal{R}$, then $$\text{$\varepsilon$-competent at }\varepsilon=0
\iff
\text{competent for exact relation }\mathcal{R}.$$ Moreover, $\varepsilon$-competence implies integrity for the corresponding $\mathcal{R}_\varepsilon$.
:::

::: proposition
[]{#prop:integrity-competence-separation label="prop:integrity-competence-separation"} Integrity and competence are distinct predicates: integrity constrains asserted outputs, while competence adds non-abstaining coverage under resource bounds.
:::

::: proof
*Proof.* Take the always-abstain solver $Q_\bot(x)=\mathsf{ABSTAIN}$ with any polynomial-time checker $V$. Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"} holds vacuously, so $(Q_\bot,V)$ is integrity-preserving, but it fails Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"} whenever $\mathcal{X}_\Gamma\neq\emptyset$ because coverage fails. Hence integrity does not imply competence. The converse is immediate because competence includes integrity as a conjunct. ◻
:::

::: definition
[]{#def:attempted-competence-failure label="def:attempted-competence-failure"} Fix an exact objective under regime $\Gamma$. A solver state is an *attempted competence failure* if:

-   integrity holds (Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"}),

-   exact competence was actually attempted for the active scope/objective,

-   competence on $\Gamma$ fails for that exact objective (Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}).
:::

::: proposition
[]{#prop:attempted-competence-matrix label="prop:attempted-competence-matrix"} Let $I,A,C\in\{0,1\}$ denote integrity, attempted exact competence, and competence available in the active regime. Policy verdict for persistent over-specification is:

-   if $I=0$: inadmissible,

-   if $I=1$ and $(A,C)=(1,0)$: conditionally rational,

-   if $I=1$ and $(A,C)\in\{(0,0),(0,1),(1,1)\}$: irrational for the same verified-cost objective.

Hence, in the integrity-preserving plane ($I=1$), exactly one cell is rational and three are irrational.
:::

This separation plus Proposition [\[prop:attempted-competence-matrix\]](#prop:attempted-competence-matrix){reference-type="ref" reference="prop:attempted-competence-matrix"} is load-bearing for the regime-conditional trilemma used later: if exact competence is blocked by hardness in a declared regime after an attempted exact procedure, integrity forces one of three responses---abstain, weaken guarantees, or change regime assumptions. \[D:prop:attempted-competence-matrix; R:\[R=active declared regime\]\]

#### Mechanized status.

This separation is machine-checked in `DecisionQuotient/IntegrityCompetence.lean` via: `competence_implies_integrity` and `integrity_not_competent_of_nonempty_scope`; the attempted-competence matrix is mechanized via `overModelVerdict_rational_iff`, `admissible_matrix_counts`, and `admissible_irrational_strictly_more_than_rational`.

::: proposition
[]{#prop:integrity-resource-bound label="prop:integrity-resource-bound"} Let $\Gamma$ be a declared regime whose in-scope family includes all instances of SUFFICIENCY-CHECK and whose declared resource bound is polynomial in the encoding length. If $P\neq coNP$, then no certifying solver is simultaneously integrity-preserving and competent on $\Gamma$ for exact sufficiency. Equivalently, for every integrity-preserving solver, at least one of the competence conjuncts must fail on $\Gamma$: either full non-abstaining coverage fails or the declared budget bound fails.
:::

::: proof
*Proof.* By Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}, competence on $\Gamma$ requires integrity, full in-scope coverage, and budget compliance. Under the coNP-hardness transfer for SUFFICIENCY-CHECK (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), universal competence on this scope would induce a polynomial-time collapse to $P=coNP$. Therefore, under $P\neq coNP$, the full competence predicate cannot hold. Since integrity alone is satisfiable (Proposition [\[prop:integrity-competence-separation\]](#prop:integrity-competence-separation){reference-type="ref" reference="prop:integrity-competence-separation"}, via always-abstain), the obstruction is exactly competence coverage/budget under the declared regime. \[D:thm:sufficiency-conp, prop:integrity-competence-separation, prop:integrity-resource-bound; R:\[R=active declared regime\]\] ◻
:::


# Computational Complexity of Decision-Relevant Uncertainty {#sec:hardness}

This section establishes the computational complexity of information sufficiency---formalized as coordinate sufficiency---for an arbitrary decision problem $\mathcal{D}$ with factored state space. Because the problems below are parameterized by $\mathcal{D}$, and the $(A, S, U)$ tuple captures any problem with choices under structured information (Remark [\[rem:universality\]](#rem:universality){reference-type="ref" reference="rem:universality"}), the hardness results are universal: they apply to every problem with coordinate structure, not to a specific problem domain. We prove three main results:

1.  **SUFFICIENCY-CHECK** is coNP-complete

2.  **MINIMUM-SUFFICIENT-SET** is coNP-complete (the $\Sigma_2^P$ structure collapses)

3.  **ANCHOR-SUFFICIENCY** (fixed coordinates) is $\Sigma_2^P$-complete

Under the model contract of Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"} and the succinct encoding of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}, these results place exact relevance identification beyond NP-completeness: in the worst case, finding (or certifying) minimal decision-relevant sets is computationally intractable.

#### Reading convention for this section.

Each hardness theorem below is paired with a recovery boundary for the same decision question: when structural-access assumptions in Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} hold, polynomial-time exact procedures are recovered; when they fail in \[S\], the stated hardness applies.

## Problem Definitions

::: definition
A *decision problem instance* is a tuple $(A, X_1, \ldots, X_n, U)$ where:

-   $A$ is a finite set of alternatives

-   $X_1, \ldots, X_n$ are the coordinate domains, with state space $S = X_1 \times \cdots \times X_n$

-   $U: A \times S \to \mathbb{Q}$ is the utility function (in the succinct encoding, $U$ is given as a Boolean circuit)
:::

#### Succinct/circuit encoding.

When $U$ is given succinctly as a Boolean or arithmetic circuit, the instance size refers to the circuit description rather than the (possibly exponentially large) truth table. Evaluating $U(a,s)$ on a single pair $(a,s)$ can be done in time polynomial in the circuit size, but quantification over all states (for example, \"for all $s$\") ranges over an exponentially large domain and is the source of the hardness results below.

::: definition
For state $s \in S$, define: $$\text{Opt}(s) := \arg\max_{a \in A} U(a, s)$$
:::

::: definition
A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if: $$\forall s, s' \in S: \quad s_I = s'_I \implies \text{Opt}(s) = \text{Opt}(s')$$ where $s_I$ denotes the projection of $s$ onto coordinates in $I$.
:::

::: problem
**Input:** Decision problem $(A, X_1, \ldots, X_n, U)$ and coordinate set $I \subseteq \{1,\ldots,n\}$\
**Question:** Is $I$ sufficient?
:::

::: problem
**Input:** Decision problem $(A, X_1, \ldots, X_n, U)$ and integer $k$\
**Question:** Does there exist a sufficient set $I$ with $|I| \leq k$?
:::

## Hardness of SUFFICIENCY-CHECK

::: theorem
[]{#thm:sufficiency-conp label="thm:sufficiency-conp"} SUFFICIENCY-CHECK is coNP-complete [@cook1971complexity; @karp1972reducibility].
:::

::: center
  Source                 Target               Key property preserved
  ---------------------- -------------------- --------------------------------------
  TAUTOLOGY              SUFFICIENCY-CHECK    Tautology iff $\emptyset$ sufficient
  $\exists\forall$-SAT   ANCHOR-SUFFICIENCY   Witness anchors iff formula true
:::

::: proof
*Proof.* extbfMembership in coNP: The complementary problem INSUFFICIENCY is in NP. A nondeterministic verifier can check a witness pair $(s,s')$ as follows:

1.  Verify $s_I = s'_I$ by projecting and comparing coordinates; this takes time polynomial in the input size.

2.  Evaluate $U$ on every alternative for both $s$ and $s'$. When $U$ is given as a circuit each evaluation runs in time polynomial in the circuit size; using these values the verifier checks whether $\text{Opt}(s) \neq \text{Opt}(s')$.

Hence INSUFFICIENCY is in NP and SUFFICIENCY-CHECK is in coNP.

**coNP-hardness:** We reduce from TAUTOLOGY.

Given Boolean formula $\varphi(x_1, \ldots, x_n)$, construct a decision problem with:

-   Alternatives: $A = \{\text{accept}, \text{reject}\}$

-   State space: $S = \{\text{reference}\} \cup \{0,1\}^n$ (equivalently, encode this as a product space with one extra coordinate $r \in \{0,1\}$ indicating whether the state is the reference state)

-   Utility: $$\begin{aligned}
            U(\text{accept}, \text{reference}) &= 1 \\
            U(\text{reject}, \text{reference}) &= 0 \\
            U(\text{accept}, a) &= \varphi(a) \\
            U(\text{reject}, a) &= 0 \quad \text{for assignments } a \in \{0,1\}^n
        
    \end{aligned}$$

-   Query set: $I = \emptyset$

**Claim:** $I = \emptyset$ is sufficient $\iff$ $\varphi$ is a tautology.

($\Rightarrow$) Suppose $I$ is sufficient. Then $\text{Opt}(s)$ is constant over all states. Since $U(\text{accept}, a) = \varphi(a)$ and $U(\text{reject}, a) = 0$:

-   $\text{Opt}(a) = \text{accept}$ when $\varphi(a) = 1$

-   $\text{Opt}(a) = \{\text{accept}, \text{reject}\}$ when $\varphi(a) = 0$

For $\text{Opt}$ to be constant, $\varphi(a)$ must be true for all assignments $a$; hence $\varphi$ is a tautology.

($\Leftarrow$) If $\varphi$ is a tautology, then $U(\text{accept}, a) = 1 > 0 = U(\text{reject}, a)$ for all assignments $a$. Thus $\text{Opt}(s) = \{\text{accept}\}$ for all states $s$, making $I = \emptyset$ sufficient. ◻
:::

#### Immediate recovery boundary (SUFFICIENCY-CHECK).

Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} is the \[S\] general-case hardness statement. For the same sufficiency relation, Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} gives polynomial-time recovery under explicit-state, separable, and tree-structured regimes.

#### Mechanized strengthening (all coordinates relevant).

The reduction above establishes coNP-hardness using a single witness set $I=\emptyset$. For the ETH-based lower bound in Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}, we additionally need worst-case instances where the minimal sufficient set has *linear* size.

We formalized a strengthened reduction in Lean 4: given a Boolean formula $\varphi$ over $n$ variables, construct a decision problem with $n$ coordinates such that if $\varphi$ is not a tautology then *every* coordinate is decision-relevant (so $k^* = n$). Intuitively, the construction places a copy of the base gadget at each coordinate and makes the global "accept" condition hold only when every coordinate's local test succeeds; a single falsifying assignment at one coordinate therefore changes the global optimal set, witnessing that coordinate's relevance. This strengthening is mechanized in Lean; see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}.

## Complexity of MINIMUM-SUFFICIENT-SET

::: theorem
[]{#thm:minsuff-conp label="thm:minsuff-conp"} MINIMUM-SUFFICIENT-SET is coNP-complete.
:::

::: proof
*Proof.* **Structural observation:** The $\exists\forall$ quantifier pattern suggests $\Sigma_2^P$: $$\exists I \, (|I| \leq k) \; \forall s, s' \in S: \quad s_I = s'_I \implies \text{Opt}(s) = \text{Opt}(s')$$ However, this collapses because sufficiency has a simple characterization.

**Key lemma:** In the Boolean-coordinate collapse model, a coordinate set $I$ is sufficient if and only if $I$ contains all relevant coordinates (proven formally as `sufficient_iff_relevant_subset` / `sufficient_iff_relevantFinset_subset` in Lean): $$\text{sufficient}(I) \iff \text{Relevant} \subseteq I$$ where $\text{Relevant} = \{i : \exists s, s'.\; s \text{ differs from } s' \text{ only at } i \text{ and } \text{Opt}(s) \neq \text{Opt}(s')\}$. This is the same relevance object as Definition [\[def:relevant\]](#def:relevant){reference-type="ref" reference="def:relevant"}; Proposition [\[prop:minimal-relevant-equiv\]](#prop:minimal-relevant-equiv){reference-type="ref" reference="prop:minimal-relevant-equiv"} gives the minimal-set equivalence in the product-space semantics used by the collapse.

**Consequence:** The minimum sufficient set is exactly the relevant-coordinate set. Thus MINIMUM-SUFFICIENT-SET asks: "Is the number of relevant coordinates at most $k$?"

**coNP membership:** A witness that the answer is NO is a set of $k+1$ coordinates, each proven relevant (by exhibiting $s, s'$ pairs). Verification is polynomial.

**coNP-hardness:** The $k=0$ case asks whether no coordinates are relevant, i.e., whether $\emptyset$ is sufficient. This is exactly SUFFICIENCY-CHECK, which is coNP-complete by Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}. ◻
:::

#### Immediate recovery boundary (MINIMUM-SUFFICIENT-SET).

Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} pairs with Theorem [\[thm:minsuff-collapse\]](#thm:minsuff-collapse){reference-type="ref" reference="thm:minsuff-collapse"}: exact minimization complexity is governed by relevance-cardinality once the collapse is applied. Recovery then depends on computing relevance efficiently, with structured-access assumptions from Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} giving the corresponding route for the underlying sufficiency computations.

## Anchor Sufficiency (Fixed Coordinates)

We also formalize a strengthened variant that fixes the coordinate set and asks whether there exists an *assignment* to those coordinates that makes the optimal action constant on the induced subcube.

::: problem
**Input:** Decision problem $(A, X_1, \ldots, X_n, U)$ and fixed coordinate set $I \subseteq \{1,\ldots,n\}$\
**Question:** Does there exist an assignment $\alpha$ to $I$ such that $\text{Opt}(s)$ is constant for all states $s$ with $s_I = \alpha$?
:::

::: theorem
[]{#thm:anchor-sigma2p label="thm:anchor-sigma2p"} ANCHOR-SUFFICIENCY is $\Sigma_2^P$-complete [@stockmeyer1976polynomial] (already for Boolean coordinate spaces).
:::

::: proof
*Proof.* **Membership in $\Sigma_2^P$:** The problem has the form $$\exists \alpha \;\forall s \in S: \; (s_I = \alpha) \implies \text{Opt}(s) = \text{Opt}(s_\alpha),$$ which is an $\exists\forall$ pattern.

**$\Sigma_2^P$-hardness:** Reduce from $\exists\forall$-SAT. Given $\exists x \, \forall y \, \varphi(x,y)$ with $x \in \{0,1\}^k$ and $y \in \{0,1\}^m$, if $m=0$ we first pad with a dummy universal variable (satisfiability is preserved), construct a decision problem with:

-   Actions $A = \{\text{YES}, \text{NO}\}$

-   State space $S = \{0,1\}^{k+m}$ representing $(x,y)$

-   Utility $$U(\text{YES}, (x,y)) =
          \begin{cases}
            2 & \text{if } \varphi(x,y)=1 \\
            0 & \text{otherwise}
          \end{cases}
        \quad
        U(\text{NO}, (x,y)) =
          \begin{cases}
            1 & \text{if } y = 0^m \\
            0 & \text{otherwise}
          \end{cases}$$

-   Fixed coordinate set $I$ = the $x$-coordinates.

If $\exists x^\star \, \forall y \, \varphi(x^\star,y)=1$, then for any $y$ we have $U(\text{YES})=2$ and $U(\text{NO})\le 1$, so $\text{Opt}(x^\star,y)=\{\text{YES}\}$ is constant. Conversely, fix $x$ and suppose $\exists y_f$ with $\varphi(x,y_f)=0$.

-   If $\varphi(x,0^m)=1$, then $\text{Opt}(x,0^m)=\{\text{YES}\}$. The falsifying assignment must satisfy $y_f\neq 0^m$, where $U(\text{YES})=U(\text{NO})=0$, so $\text{Opt}(x,y_f)=\{\text{YES},\text{NO}\}$.

-   If $\varphi(x,0^m)=0$, then $\text{Opt}(x,0^m)=\{\text{NO}\}$. After padding we have $m>0$, so choose any $y'\neq 0^m$: either $\varphi(x,y')=1$ (then $\text{Opt}(x,y')=\{\text{YES}\}$) or $\varphi(x,y')=0$ (then $\text{Opt}(x,y')=\{\text{YES},\text{NO}\}$). In both subcases the optimal set differs from $\{\text{NO}\}$.

Hence the subcube for this $x$ is not constant. Thus an anchor assignment exists iff the $\exists\forall$-SAT instance is true. ◻
:::

#### Immediate boundary statement (ANCHOR-SUFFICIENCY).

Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"} remains a second-level hardness statement in the anchored formulation; unlike MINIMUM-SUFFICIENT-SET, no general collapse to relevance counting is established here, so the corresponding tractability status remains open in this model.

## Tractable Subcases

Despite the general hardness, several natural subcases admit efficient algorithms:

::: proposition
When $|S|$ is polynomial in the input size (i.e., explicitly enumerable), MINIMUM-SUFFICIENT-SET is solvable in polynomial time.
:::

::: proof
*Proof.* Compute $\text{Opt}(s)$ for all $s \in S$. The minimum sufficient set is exactly the set of coordinates that "matter" for the resulting function, computable by standard techniques. ◻
:::

::: proposition
When $U(a, s) = w_a \cdot s$ for weight vectors $w_a \in \mathbb{Q}^n$, MINIMUM-SUFFICIENT-SET reduces to identifying coordinates where weight vectors differ.
:::

## Implications

::: corollary
Under the succinct encoding, exact minimization of sufficient coordinate sets is coNP-hard via the $k=0$ case, and fixed-anchor minimization is $\Sigma_2^P$-complete.
:::

::: proof
*Proof.* The $k=0$ case of MINIMUM-SUFFICIENT-SET is SUFFICIENCY-CHECK (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), giving coNP-hardness for exact minimization. The fixed-anchor variant is exactly Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"}. ◻
:::

The modeling budget for deciding what to model is therefore a computationally constrained resource under this encoding. \[D:thm:sufficiency-conp, thm:anchor-sigma2p; R:\[S\]\]

## The succinct--minimal gap and physical agents {#sec:neuro-correspondence}

In complexity theory, a *succinct* representation of a combinatorial object is a Boolean circuit of size $\mathrm{poly}(n)$ that computes a function whose explicit (truth-table) form has size $2^{\Theta(n)}$. The term is standard but informal: it denotes a size class (polynomial in input variables), not a structural property. In particular, "succinct" does not mean *minimal*. The minimal circuit for a function is the smallest circuit that computes it, a rigorous, unique object. A succinct circuit may be far larger than the minimal one while still qualifying as "succinct" by the poly-size criterion.

#### The gap.

Let $C$ be a succinct circuit computing a utility function $U$, and let $C^*$ be the minimal circuit for the same function. The *representation gap* $\varepsilon = |C| - |C^*|$ measures how far the agent's encoding is from the tightest possible encoding. This gap has no standard formal definition in the literature; it is the unnamed distance between an informal size class and a rigorous structural minimum.

::: proposition
[]{#prop:representation-gap label="prop:representation-gap"} In the Boolean-coordinate model, let $R_{\mathrm{rel}}=\texttt{relevantFinset}(dp)$ and define $$\varepsilon(I)\;:=\;|I\setminus R_{\mathrm{rel}}| + |R_{\mathrm{rel}}\setminus I|.$$ Then: $$\varepsilon(I)=0 \iff I=R_{\mathrm{rel}}
\iff I \text{ is minimal sufficient}.$$
:::

The results of this paper give $\varepsilon$ formal complexity consequences. By Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}, determining the minimal sufficient coordinate set is coNP-complete under the succinct encoding. By Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}, under ETH there exist succinct instances requiring $2^{\Omega(n)}$ time to verify sufficiency. In the formal Boolean-coordinate collapse model, size-bounded $\varepsilon=0$ search is exactly the relevance-cardinality predicate (*Lean:* `Sigma2PHardness.min_representationGap_zero_iff_relevant_card`). Together: for an agent encoded as a succinct circuit, the worst-case cost of determining whether its own coordinate attention set is minimal is exponential in the number of input coordinates (under ETH). The gap $\varepsilon$ is not merely unnamed; it is *computationally irreducible*: no polynomial-time algorithm solves all succinct instances (assuming $\mathrm{P} \neq coNP$), and the hard instance family requires $2^{\Omega(n)}$ time.

#### Physical agents as circuits.

Any physical agent that selects actions based on sensory state can be modeled, in the static snapshot, as a circuit: sensory inputs are coordinates $X_1, \ldots, X_n$; the agent's internal computation maps states to actions; and the quality of that mapping is measured by a utility function $U$. \[D:prop:snapshot-process-typing, prop:bridge-transfer-scope; R:\[bridge-admissible snapshot\]\] The explicit-state encoding (truth table) of this mapping has size exponential in the number of sensory dimensions. No physical agent can store it. \[D:thm:dichotomy; R:\[E\] vs \[S+ETH\]\] Every physical agent is therefore a succinct encoding, a circuit whose size is bounded by physical resources (neurons, synapses, transistors, parameters) rather than by the size of the state space it navigates. \[D:thm:dichotomy; R:\[S\]\]

This is not a metaphor. A biological nervous system is a feedforward or recurrent circuit that takes sensory state as input and produces motor commands as output. \[D:prop:snapshot-process-typing; R:\[represented adjacent class\]\] A trained neural network is a parameterized circuit. \[D:prop:snapshot-process-typing; R:\[represented adjacent class\]\] In both cases, the agent *is* a succinct encoding of a utility-to-action mapping, and the question "is this agent attending to the right inputs?" is exactly SUFFICIENCY-CHECK under the succinct encoding. \[D:thm:config-reduction, thm:sufficiency-conp; R:\[S\]\] The compression that makes a circuit physically realizable---polynomial size rather than exponential---is the same compression that makes self-verification exponentially costly in the worst case: the state space the circuit compressed away is precisely the domain that must be exhaustively checked to certify sufficiency. \[D:thm:dichotomy, prop:query-regime-obstruction; R:\[S+ETH\],\[Q_fin\]\]

#### The simplicity tax as $\varepsilon$.

The simplicity tax (Definition [\[def:simplicity-tax\]](#def:simplicity-tax){reference-type="ref" reference="def:simplicity-tax"}) measures $|\mathrm{Gap}(M,P)| = |R(P) \setminus A(M)|$: the number of decision-relevant coordinates that the agent's model does not handle natively. In the $\varepsilon$ decomposition above, this is exactly the unattended-relevant component $|R_{\mathrm{rel}}\setminus I|$ (*Lean:* `Sigma2PHardness.representationGap_missing_eq_gapCard`, `Sigma2PHardness.representationGap_eq_waste_plus_missing`). For a physical agent modeled as a circuit, this is the coordinate-level manifestation of $\varepsilon$: the agent attends to a superset of what is necessary, or fails to attend to coordinates that are relevant, and faces worst-case cost exponential in $n$ to verify which case holds (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}). Theorem [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"} then says the total relevance budget is conserved: unhandled coordinates are not eliminated, only redistributed as external per-site cost.

#### Consequences for learned circuits.

Large language models and deep networks are succinct circuits with $\mathrm{poly}(n)$ parameters. \[D:thm:dichotomy; R:\[S\]\] Mechanistic interpretability asks which internal components (attention heads, neurons, layers) are necessary for a given capability; this is SUFFICIENCY-CHECK applied to the circuit's internal coordinate structure. Pruning research asks for the minimal subcircuit that preserves performance; this is MINIMUM-SUFFICIENT-SET. The results of this paper imply that these questions are coNP-hard in the worst case under succinct encoding. \[D:thm:sufficiency-conp, thm:minsuff-conp; R:\[S\]\] Empirical progress on interpretability and pruning therefore depends on exploiting the structural properties of specific trained circuits (analogous to the tractable subcases of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}), not on solving the general problem. \[D:thm:sufficiency-conp, thm:tractable; R:\[S\] vs \[tractable regimes\]\]

#### Scope and caveats.

The formal results above apply to the static, deterministic model fixed by C1--C4 (Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"}). Biological neural systems add noise, temporal dynamics, and synaptic plasticity; trained networks add stochastic optimization and distribution shift. These factors may alter empirical tractability relative to the static worst-case bounds. The bridge conditions of Proposition [\[prop:one-step-bridge\]](#prop:one-step-bridge){reference-type="ref" reference="prop:one-step-bridge"} delineate when static sufficiency results transfer to sequential settings; beyond those conditions, the governing complexity objects change (Propositions [\[prop:bridge-failure-horizon\]](#prop:bridge-failure-horizon){reference-type="ref" reference="prop:bridge-failure-horizon"}--[\[prop:bridge-failure-transition\]](#prop:bridge-failure-transition){reference-type="ref" reference="prop:bridge-failure-transition"}). The claims in this subsection are therefore regime-typed consequences of the formal results, not universal assertions about all possible agent architectures. \[D:prop:one-step-bridge, thm:bridge-boundary-represented, prop:snapshot-process-typing; R:\[represented adjacent class\]\]

## Quantifier Collapse for MINIMUM-SUFFICIENT-SET

::: theorem
[]{#thm:minsuff-collapse label="thm:minsuff-collapse"} The apparent second-level predicate $$\exists I \, (|I| \leq k) \; \forall s,s' \in S:\; s_I = s'_I \implies \operatorname{Opt}(s)=\operatorname{Opt}(s')$$ is equivalent to the coNP predicate $|\text{Relevant}| \le k$, where $$\text{Relevant} = \{i : \exists s,s'.\; s \text{ differs from } s' \text{ only at } i \text{ and } \operatorname{Opt}(s)\neq\operatorname{Opt}(s')\}.$$ Consequently, MINIMUM-SUFFICIENT-SET is governed by coNP certificates rather than a genuine $\Sigma_2^P$ alternation.
:::

::: proof
*Proof.* By the formal equivalence `sufficient_iff_relevant_subset` (finite-set form `sufficient_iff_relevantFinset_subset`), a coordinate set $I$ is sufficient iff $\text{Relevant}\subseteq I$. Therefore: $$\exists I \; (|I|\le k \wedge \text{sufficient}(I))
\iff
\exists I \; (|I|\le k \wedge \text{Relevant}\subseteq I)
\iff
|\text{Relevant}| \le k.$$ So the existential-over-universal presentation collapses to counting the relevant coordinates.

A NO certificate for $|\text{Relevant}| \le k$ is a list of $k+1$ distinct relevant coordinates, each witnessed by two states that differ only on that coordinate and yield different optimal sets; this is polynomially verifiable. Hence the resulting predicate is in coNP, matching Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}.

This also clarifies why ANCHOR-SUFFICIENCY remains $\Sigma_2^P$-complete: once an anchor assignment is existentially chosen, the universal quantifier over the residual subcube does not collapse to a coordinate-counting predicate. ◻
:::


# Encoding-Regime Separation {#sec:dichotomy}

The hardness results of Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} apply to worst-case instances under the succinct encoding. This section states an encoding-regime separation: an explicit-state upper bound versus a succinct-encoding worst-case lower bound, and an intermediate query-access obstruction family. The complexity class is a property of the encoding measured against a fixed decision question (Remark [\[rem:question-vs-problem\]](#rem:question-vs-problem){reference-type="ref" reference="rem:question-vs-problem"}), not a property of the question itself: the same sufficiency question admits polynomial-time algorithms under one encoding and worst-case exponential cost under another.

#### Model note.

Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} has Part 1 in \[E\] (time polynomial in $|S|$) and Part 2 in \[S+ETH\] (time exponential in $n$). Proposition [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"} is \[Q_fin\] (finite-state Opt-oracle core), while Propositions [\[prop:query-value-entry-lb\]](#prop:query-value-entry-lb){reference-type="ref" reference="prop:query-value-entry-lb"} and [\[prop:query-state-batch-lb\]](#prop:query-state-batch-lb){reference-type="ref" reference="prop:query-state-batch-lb"} are \[Q_bool\] interface refinements (value-entry and state-batch). Relative to Definition [\[def:regime-simulation\]](#def:regime-simulation){reference-type="ref" reference="def:regime-simulation"}, Propositions [\[prop:query-subproblem-transfer\]](#prop:query-subproblem-transfer){reference-type="ref" reference="prop:query-subproblem-transfer"} and [\[prop:oracle-lattice-transfer\]](#prop:oracle-lattice-transfer){reference-type="ref" reference="prop:oracle-lattice-transfer"} are explicit simulation-transfer instances. The \[E\] vs \[S+ETH\] split in Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} is a same-question encoding/cost-model separation, not a bidirectional simulation claim between those regimes. These regimes are defined in Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"} and are not directly comparable as functions of one numeric input-length parameter.

::: theorem
[]{#thm:dichotomy label="thm:dichotomy"} Let $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ be a decision problem with $|S| = N$ states. Let $k^*$ be the size of the minimal sufficient set.

1.  **\[E\] Explicit-state upper bound:** Under the explicit-state encoding, SUFFICIENCY-CHECK is solvable in time polynomial in $N$ (e.g. $O(N^2|A|)$).

2.  **\[S+ETH\] Succinct lower bound (worst case):** Assuming ETH, there exists a family of succinctly encoded instances with $n$ coordinates and minimal sufficient set size $k^* = n$ such that SUFFICIENCY-CHECK requires time $2^{\Omega(n)}$.
:::

::: proof
*Proof.* **Part 1 (Explicit-state upper bound):** Under the explicit-state encoding, SUFFICIENCY-CHECK is decidable in time polynomial in $N$ by direct enumeration: compute $\operatorname{Opt}(s)$ for all $s\in S$ and then check all pairs $(s,s')$ with $s_I=s'_I$.

Equivalently, for any fixed $I$, the projection map $s\mapsto s_I$ has image size $|S_I|\le |S|=N$, so any algorithm that iterates over projection classes (or over all state pairs) runs in polynomial time in $N$. Thus, in particular, when $k^*=O(\log N)$, SUFFICIENCY-CHECK is solvable in polynomial time under the explicit-state encoding.

#### Remark (bounded coordinate domains).

In the general model $S=\prod_i X_i$, for a fixed $I$ one always has $|S_I|\le \prod_{i\in I}|X_i|$ (and $|S_I|\le N$). If the coordinate domains are uniformly bounded, $|X_i|\le d$ for all $i$, then $|S_I|\le d^{|I|}$.

**Part 2 (Succinct ETH lower bound, worst case):** A strengthened version of the TAUTOLOGY reduction used in Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} produces a family of instances in which the minimal sufficient set has size $k^* = n$: given a Boolean formula $\varphi$ over $n$ variables, we construct a decision problem with $n$ coordinates such that if $\varphi$ is not a tautology then *every* coordinate is decision-relevant (thus $k^*=n$). This strengthening is mechanized in Lean (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}). Under the Exponential Time Hypothesis (ETH) [@impagliazzo2001complexity], TAUTOLOGY requires time $2^{\Omega(n)}$ in the succinct encoding, so SUFFICIENCY-CHECK inherits a $2^{\Omega(n)}$ worst-case lower bound via this reduction. ◻
:::

::: corollary
There is a clean separation between explicit-state tractability and succinct worst-case hardness (with respect to the encodings in Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}):

-   Under the explicit-state encoding, SUFFICIENCY-CHECK is polynomial in $N=|S|$.

-   Under ETH, there exist succinctly encoded instances with $k^* = \Omega(n)$ (indeed $k^*=n$) for which SUFFICIENCY-CHECK requires $2^{\Omega(n)}$ time.

For Boolean coordinate spaces ($N = 2^n$), the explicit-state bound is polynomial in $2^n$ (exponential in $n$), while under ETH the succinct lower bound yields $2^{\Omega(n)}$ time for the hard family in which $k^* = \Omega(n)$.
:::

::: proposition
[]{#prop:query-regime-obstruction label="prop:query-regime-obstruction"} In the finite-state query regime \[Q_fin\], let $S$ be any finite state type with $|S|\ge 2$ and let $Q\subset S$ with $|Q|<|S|$. Then there exist two decision problems $\mathcal{D}_{\mathrm{yes}},\mathcal{D}_{\mathrm{no}}$ over the same state space such that:

-   their oracle views on all states in $Q$ are identical,

-   $\emptyset$ is sufficient for $\mathcal{D}_{\mathrm{yes}}$,

-   $\emptyset$ is not sufficient for $\mathcal{D}_{\mathrm{no}}$.

Consequently, no deterministic query procedure using fewer than $|S|$ state queries can solve SUFFICIENCY-CHECK on all such instances; the worst-case query complexity is $\Omega(|S|)$.
:::

::: proof
*Proof.* This is exactly the finite-state indistinguishability theorem `ClaimClosure.query_obstruction_finite_state_core`. For any $|Q|<|S|$, there is an unqueried hidden state $s_0$ producing oracle-indistinguishable yes/no instances with opposite truth values on the $I=\emptyset$ subproblem. Since SUFFICIENCY-CHECK contains that subproblem, fewer than $|S|$ queries cannot be correct on both instances, yielding the $\Omega(|S|)$ worst-case lower bound. ◻
:::

::: corollary
[]{#cor:query-obstruction-bool label="cor:query-obstruction-bool"} In the Boolean-coordinate state space $S=\{0,1\}^n$, Proposition [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"} yields the familiar $\Omega(2^n)$ worst-case query lower bound for Opt-oracle access.
:::

::: proposition
[]{#prop:query-value-entry-lb label="prop:query-value-entry-lb"} In the mechanized Boolean value-entry query submodel \[Q_bool\], for any deterministic procedure using fewer than $2^n$ value-entry queries $(a,s)\mapsto U(a,s)$, there exist two queried-value-indistinguishable instances with opposite truth values for SUFFICIENCY-CHECK on the $I=\emptyset$ subproblem. Therefore worst-case value-entry query complexity is also $\Omega(2^n)$.
:::

::: proof
*Proof.* The theorem `emptySufficiency_valueEntry_indistinguishable_pair` constructs, for any query set of cardinality $<2^n$, an unqueried hidden state $s_0$ and a yes/no instance pair that agree on all queried values but disagree on $\emptyset$-sufficiency. The auxiliary bound `touchedStates_card_le_query_card` ensures that fewer than $2^n$ value-entry queries cannot cover all states, so the indistinguishability argument applies in the worst case. ◻
:::

::: proposition
[]{#prop:query-subproblem-transfer label="prop:query-subproblem-transfer"} If every full-problem solver induces a solver for a fixed subproblem, then any lower bound for that subproblem lifts to the full problem.
:::

This is the restriction-map instance of Definition [\[def:regime-simulation\]](#def:regime-simulation){reference-type="ref" reference="def:regime-simulation"}: a solver for the full regime induces one for the restricted subproblem regime, so lower bounds transfer.

::: proposition
[]{#prop:query-randomized-robustness label="prop:query-randomized-robustness"} In \[Q_bool\], for any query set with cardinality $<2^n$, the indistinguishable yes/no pair from Proposition [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"} forces one decoding error *per random seed* for any seed-indexed decoder from oracle transcripts. Consequently, finite-support randomization does not remove the obstruction: averaging preserves a constant error floor on the hard pair.
:::

::: proposition
[]{#prop:query-randomized-weighted label="prop:query-randomized-weighted"} For any finite-support seed weighting $\mu$, the same hard pair satisfies a weighted identity: the weighted sum of yes-error and no-error equals total seed weight. Hence randomization cannot collapse both errors simultaneously.
:::

::: proposition
[]{#prop:query-state-batch-lb label="prop:query-state-batch-lb"} In \[Q_bool\], the same $\Omega(2^n)$ lower bound holds for a state-batch oracle that returns the full Boolean-action utility tuple at each queried state.
:::

::: proposition
[]{#prop:query-finite-state-generalization label="prop:query-finite-state-generalization"} The empty-subproblem indistinguishability lower-bound core extends from Boolean-vector state spaces to any finite state type with at least two states.
:::

::: proposition
[]{#prop:query-tightness-full-scan label="prop:query-tightness-full-scan"} For the const/spike adversary family used in the query lower bounds, querying all states distinguishes the pair; thus the lower-bound family is tight up to constant factors under full-state scan.
:::

::: proposition
[]{#prop:query-weighted-transfer label="prop:query-weighted-transfer"} Let $w(q)$ be per-query cost and $w_{\min}$ a lower bound on all queried costs. Any cardinality lower bound $|Q|\geq L$ lifts to weighted cost: $$\sum_{q\in Q} w(q)\ \ge\ w_{\min}\cdot L.$$
:::

::: proposition
[]{#prop:oracle-lattice-transfer label="prop:oracle-lattice-transfer"} In \[Q_bool\], agreement on state-batch oracle views over touched states implies agreement on all value-entry views for the corresponding entry-query set.
:::

This is the oracle-transducer instance of Definition [\[def:regime-simulation\]](#def:regime-simulation){reference-type="ref" reference="def:regime-simulation"}: batch transcripts induce entry transcripts while preserving indistinguishability for the target sufficiency question.

::: proposition
[]{#prop:oracle-lattice-strict label="prop:oracle-lattice-strict"} 'Opt'-oracle views are strictly coarser than value-entry views: there exist instances with identical 'Opt' views but distinguishable value entries.
:::

::: remark
Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} and Propositions [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"}--[\[prop:query-value-entry-lb\]](#prop:query-value-entry-lb){reference-type="ref" reference="prop:query-value-entry-lb"} keep the structural problem fixed (same sufficiency relation) and separate representational hardness by access regime: explicit-state access exposes the boundary $s \mapsto \operatorname{Opt}(s)$, finite-state query access already yields $\Omega(|S|)$ lower bounds at the Opt-oracle level (Boolean instantiation: $\Omega(2^n)$), value-entry/state-batch interfaces preserve the obstruction in \[Q_bool\], and succinct access can hide structure enough to force ETH-level worst-case cost on a hard family.
:::

This regime-typed landscape identifies tractability under \[E\], a finite-state query lower-bound core under \[Q_fin\] with Boolean interface refinements under \[Q_bool\], and worst-case intractability under \[S+ETH\] for the same underlying decision question.

The structural reason for this separation is enumerable access. Under the explicit-state encoding, the mapping $s \mapsto \operatorname{Opt}(s)$ is directly inspectable and sufficiency verification reduces to scanning state pairs, at cost polynomial in $|S|$. Under succinct encoding, the circuit compresses an exponential state space into polynomial size; universal verification over that compressed domain---"for all $s, s'$ with $s_I = s'_I$, does $\operatorname{Opt}(s) = \operatorname{Opt}(s')$?"---carries worst-case cost exponential in $n$, because the domain the circuit compressed away cannot be reconstructed without undoing the compression.


# Tractable Special Cases: When You Can Solve It {#sec:tractable}

We distinguish the encodings of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. The tractability results below state the model assumption explicitly. Structural insight: hardness dissolves exactly when the full decision boundary $s \mapsto \operatorname{Opt}(s)$ is recoverable in polynomial time from the input representation; the three cases below instantiate this single principle. Concretely, each tractable regime corresponds to a specific structural insight (explicit boundary exposure, additive separability, or tree factorization) that removes the hardness witness; this supports reading the general-case hardness as missing structural access in the current representation rather than as an intrinsic semantic barrier.

::: theorem
[]{#thm:tractable label="thm:tractable"} SUFFICIENCY-CHECK is polynomial-time solvable in the following cases:

1.  **Explicit-state encoding:** The input contains the full utility table over $A \times S$. SUFFICIENCY-CHECK runs in $O(|S|^2|A|)$ time; if $|A|$ is constant, $O(|S|^2)$.

2.  **Separable utility (any encoding):** $U(a, s) = f(a) + g(s)$.

3.  **Tree-structured utility with explicit local factors (succinct structured encoding):** There exists a rooted tree on coordinates and local functions $u_i$ such that $$U(a,s) = \sum_i u_i\bigl(a, s_i, s_{\mathrm{parent}(i)}\bigr),$$ with the root term depending only on $(a, s_{\mathrm{root}})$ and all $u_i$ given explicitly as part of the input.
:::

## Explicit-State Encoding

::: proof
*Proof of Part 1.* Given the full table of $U(a,s)$, compute $\operatorname{Opt}(s)$ for all $s \in S$ in $O(|S||A|)$ time. For SUFFICIENCY-CHECK on a given $I$, verify that for all pairs $(s,s')$ with $s_I = s'_I$, we have $\operatorname{Opt}(s) = \operatorname{Opt}(s')$. This takes $O(|S|^2|A|)$ time by direct enumeration and is polynomial in the explicit input length. If $|A|$ is constant, the runtime is $O(|S|^2)$. ◻
:::

## Separable Utility

::: proof
*Proof of Part 2.* If $U(a, s) = f(a) + g(s)$, then: $$\operatorname{Opt}(s) = \arg\max_{a \in A} [f(a) + g(s)] = \arg\max_{a \in A} f(a)$$ The optimal action is independent of the state. Thus $I = \emptyset$ is always sufficient. ◻
:::

## Tree-Structured Utility

::: proof
*Proof of Part 3.* Assume the tree decomposition and explicit local tables as stated. For each node $i$ and each value of its parent coordinate, compute the set of actions that are optimal for some assignment of the subtree rooted at $i$. This is a bottom-up dynamic program that combines local tables with child summaries; each table lookup is explicit in the input. A coordinate is relevant if and only if varying its value changes the resulting optimal action set. The total runtime is polynomial in $n$, $|A|$, and the size of the local tables. ◻
:::

## Practical Implications

::: center
  **Condition**             **Examples**
  ------------------------- ----------------------------------------
  Explicit-state encoding   Small or fully enumerated state spaces
  Separable utility         Additive costs, linear models
  Tree-structured utility   Hierarchies, causal trees
:::

::: proposition
[]{#prop:heuristic-reusability label="prop:heuristic-reusability"} Let $\mathcal{C}$ be a structure class for which SUFFICIENCY-CHECK is polynomial (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}). If membership in $\mathcal{C}$ is decidable in polynomial time, then the combined detect-then-check procedure is a sound, polynomial-time heuristic applicable to all future instances in $\mathcal{C}$. For each subcase of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, structure detection is polynomial (under the declared representation assumptions).
:::

::: remark
Proposition [\[prop:heuristic-reusability\]](#prop:heuristic-reusability){reference-type="ref" reference="prop:heuristic-reusability"} removes the complexity-theoretic obstruction to integrity-preserving action on detectable tractable instances: integrity no longer *forces* abstention. Whether the agent acts still requires competence (Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}): budget and coverage must also be satisfied. An agent that detects structure class $\mathcal{C}$, applies the corresponding polynomial checker, and abstains when detection fails maintains integrity---it never claims sufficiency without verification. Mistaking the heuristic for the general solution---claiming polynomial-time competence on a coNP-hard problem---violates integrity (Proposition [\[prop:integrity-resource-bound\]](#prop:integrity-resource-bound){reference-type="ref" reference="prop:integrity-resource-bound"}).
:::


# Regime-Conditional Corollaries {#sec:engineering-justification}

This section derives regime-typed engineering corollaries from the core complexity theorems. Theorem [\[thm:config-reduction\]](#thm:config-reduction){reference-type="ref" reference="thm:config-reduction"} maps configuration simplification to SUFFICIENCY-CHECK; Theorems [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}, and [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} then yield exact minimization consequences under \[S\] and \[S+ETH\].

Regime tags used below follow Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"}: \[S\], \[S+ETH\], \[E\], \[S_bool\]. Any prescription that requires exact minimization is constrained by these theorem-level bounds. \[D:thm:sufficiency-conp, thm:minsuff-conp, thm:dichotomy; R:\[S\],\[S+ETH\]\] Theorem [\[thm:overmodel-diagnostic\]](#thm:overmodel-diagnostic){reference-type="ref" reference="thm:overmodel-diagnostic"} implies that persistent failure to isolate a minimal sufficient set is a boundary-characterization signal in the current model, not a universal irreducibility claim.

#### Conditional rationality criterion.

For the objective "minimize verified total cost while preserving integrity," over-specification is rational only under *attempted competence failure* in the active regime (Definition [\[def:attempted-competence-failure\]](#def:attempted-competence-failure){reference-type="ref" reference="def:attempted-competence-failure"}): if exact irrelevance cannot be certified efficiently after an attempted exact procedure, integrity forbids uncertified exclusion. \[D:prop:attempted-competence-matrix; R:\[R=active declared regime\]\] When exact competence is available in the active regime (e.g., Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} and the exact-identifiability criterion), persistent over-specification is irrational relative to that objective because proven-irrelevant coordinates can be removed with certified correctness. \[D:prop:attempted-competence-matrix, thm:tractable; R:\[E\],\[structured\]\] Proposition [\[prop:attempted-competence-matrix\]](#prop:attempted-competence-matrix){reference-type="ref" reference="prop:attempted-competence-matrix"} makes this explicit: in the integrity-preserving matrix, one cell is rational and three are irrational, so irrationality is the default verdict. \[D:prop:attempted-competence-matrix; R:\[R=active declared regime\]\]

::: remark
All claims in this section are formal corollaries under the declared model assumptions.

-   Competence claims are indexed by the regime tuple of Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}; prescriptions are meaningful only relative to feasible resources under that regime (bounded-rationality feasibility discipline) [@sep_bounded_rationality]. \[D:prop:integrity-competence-separation; R:\[R=active declared regime\]\]

-   Integrity (Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"}) forbids overclaiming beyond certifiable outputs; $\mathsf{ABSTAIN}$/$\mathsf{UNKNOWN}$ is first-class when certification is unavailable. \[D:prop:integrity-competence-separation; R:\[R=active declared regime\]\]

-   Therefore, hardness results imply a regime-conditional trilemma: abstain, weaken guarantees (heuristics/approximation), or change encoding/structural assumptions to recover competence. \[D:prop:attempted-competence-matrix, thm:sufficiency-conp, thm:dichotomy; R:\[S\],\[S+ETH\]\]
:::

## Configuration Simplification is SUFFICIENCY-CHECK

Because SUFFICIENCY-CHECK is a meta-problem parameterized by an arbitrary decision problem $\mathcal{D}$, real engineering problems with factored configuration spaces are instances of the hardness landscape established above.

::: theorem
[]{#thm:config-reduction label="thm:config-reduction"} Given a software system with configuration parameters $P = \{p_1, \ldots, p_n\}$ and observed behaviors $B = \{b_1, \ldots, b_m\}$, the problem of determining whether parameter subset $I \subseteq P$ preserves all behaviors is equivalent to SUFFICIENCY-CHECK.
:::

::: proof
*Proof.* Construct decision problem $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ where:

-   Actions $A = B \cup \{\bot\}$, where $\bot$ is a sentinel "no-observed-behavior" action

-   Coordinates $X_i$ = domain of parameter $p_i$

-   State space $S = X_1 \times \cdots \times X_n$

-   For $b\in B$, utility $U(b, s) = 1$ if behavior $b$ occurs under configuration $s$, else $0$

-   Sentinel utility $U(\bot,s)=1$ iff no behavior in $B$ occurs under configuration $s$, else $0$

Then $$\operatorname{Opt}(s)=
\begin{cases}
\{b \in B : b \text{ occurs under configuration } s\}, & \text{if this set is nonempty},\\
\{\bot\}, & \text{otherwise}.
\end{cases}$$ So the optimizer map exactly encodes observed-behavior equivalence classes, including the empty-behavior case.

Coordinate set $I$ is sufficient iff: $$s_I = s'_I \implies \operatorname{Opt}(s) = \operatorname{Opt}(s')$$

This holds iff configurations agreeing on parameters in $I$ exhibit identical behaviors.

Therefore, "does parameter subset $I$ preserve all behaviors?" is exactly SUFFICIENCY-CHECK for the constructed decision problem. ◻
:::

::: remark
The reduction above requires only:

1.  a finite behavior set,

2.  parameters with finite domains, and

3.  an evaluable behavior map from configurations to achieved behaviors.

These are exactly the model-contract premises C1--C3 instantiated for configuration systems.
:::

::: theorem
[]{#thm:overmodel-diagnostic label="thm:overmodel-diagnostic"} By contraposition of Theorem [\[thm:config-reduction\]](#thm:config-reduction){reference-type="ref" reference="thm:config-reduction"}, if no coordinate set can be certified as exactly relevance-identifying (Definition [\[def:exact-identifiability\]](#def:exact-identifiability){reference-type="ref" reference="def:exact-identifiability"}) for the modeled system, then the decision boundary is not completely characterized by the current parameterization.
:::

::: proof
*Proof.* Assume the decision boundary were completely characterized by the current parameterization. Then, via Theorem [\[thm:config-reduction\]](#thm:config-reduction){reference-type="ref" reference="thm:config-reduction"}, the corresponding sufficiency instance admits exact relevance membership, hence a coordinate set that satisfies Definition [\[def:exact-identifiability\]](#def:exact-identifiability){reference-type="ref" reference="def:exact-identifiability"}. Contraposition gives the claim: persistent failure of exact relevance identification signals incomplete characterization of decision relevance in the model. ◻
:::

## Cost Asymmetry Under ETH

We now prove a cost asymmetry result under the stated cost model and complexity constraints.[^1]

::: theorem
[]{#thm:cost-asymmetry-eth label="thm:cost-asymmetry-eth"} Consider an engineer specifying a system configuration with $n$ parameters. Let:

-   $C_{\text{over}}(k)$ = cost of maintaining $k$ extra parameters beyond minimal

-   $C_{\text{find}}(n)$ = cost of finding minimal sufficient parameter set

-   $C_{\text{under}}$ = expected cost of production failures from underspecification

Assume ETH in the succinct encoding model of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. Then:

1.  Exact identification of minimal sufficient sets has worst-case finding cost $C_{\text{find}}(n)=2^{\Omega(n)}$. (Under ETH, SUFFICIENCY-CHECK has a $2^{\Omega(n)}$ lower bound in the succinct model, and exact minimization subsumes this decision task.)

2.  Maintenance cost is linear: $C_{\text{over}}(k) = O(k)$.

3.  Under ETH, exponential finding cost dominates linear maintenance cost for sufficiently large $n$.

Therefore, there exists $n_0$ such that for all $n > n_0$, the finding-vs-maintenance asymmetry satisfies: $$C_{\text{over}}(k) < C_{\text{find}}(n) + C_{\text{under}}$$

Within \[S+ETH\], persistent over-specification is consistent with unresolved boundary characterization rather than a proof that all included parameters are intrinsically necessary. Conversely, when exact competence is available in the active regime, persistent over-specification is irrational for the same cost-minimization objective. \[D:thm:cost-asymmetry-eth, prop:attempted-competence-matrix; R:\[S+ETH\] vs \[tractable active regime\]\]
:::

::: proof
*Proof.* Under ETH, the TAUTOLOGY reduction used in Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} yields a $2^{\Omega(n)}$ worst-case lower bound for SUFFICIENCY-CHECK in the succinct encoding. Any exact algorithm that outputs a minimum sufficient set can decide whether the optimum size is $0$ by checking whether the returned set is empty; this is exactly the SUFFICIENCY-CHECK query for $I=\emptyset$. Hence exact minimal-set finding inherits the same exponential worst-case lower bound.

Maintaining $k$ extra parameters incurs:

-   Documentation cost: $O(k)$ entries

-   Testing cost: $O(k)$ test cases

-   Migration cost: $O(k)$ parameters to update

Total maintenance cost is $C_{\text{over}}(k) = O(k)$.

The eventual dominance step is mechanized in `HardnessDistribution.linear_lt_exponential_plus_constant_eventually`: for fixed linear-overhead parameter $k$ and additive constant $C_{\text{under}}$ there is $n_0$ such that $k < 2^n + C_{\text{under}}$ for all $n \ge n_0$. Therefore: $$C_{\text{over}}(k) \ll C_{\text{find}}(n)$$

For any fixed nonnegative $C_{\text{under}}$, the asymptotic dominance inequality remains and only shifts the finite threshold $n_0$. ◻
:::

::: corollary
[]{#cor:no-auto-minimize label="cor:no-auto-minimize"} Assuming $P\neq coNP$, there exists no polynomial-time algorithm that:

1.  Takes an arbitrary configuration file with $n$ parameters

2.  Identifies the minimal sufficient parameter subset

3.  Guarantees correctness (no false negatives)
:::

::: proof
*Proof.* Such an algorithm would solve MINIMUM-SUFFICIENT-SET in polynomial time, contradicting Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} (assuming $P\neq coNP$). ◻
:::

::: remark
Corollary [\[cor:no-auto-minimize\]](#cor:no-auto-minimize){reference-type="ref" reference="cor:no-auto-minimize"} is a formal boundary statement: an always-correct polynomial-time minimizer for arbitrary succinct inputs would collapse $P$ and $coNP$.
:::

::: remark
The practical force of worst-case hardness depends on instance structure, especially $k^*$. If SUFFICIENCY-CHECK is FPT in parameter $k^*$, then small-$k^*$ families can remain tractable even under succinct encodings. The strengthened mechanized gadget (`all_coords_relevant_of_not_tautology`) still proves existence of hard families with $k^*=n$; what is typical in deployed systems is an empirical question outside this formal model.
:::

## Regime-Conditional Operational Corollaries

Theorems [\[thm:overmodel-diagnostic\]](#thm:overmodel-diagnostic){reference-type="ref" reference="thm:overmodel-diagnostic"} and [\[thm:cost-asymmetry-eth\]](#thm:cost-asymmetry-eth){reference-type="ref" reference="thm:cost-asymmetry-eth"} yield the following conditional operational consequences:

**1. Conservative retention under unresolved relevance.** If irrelevance cannot be certified efficiently under the active regime, retaining a superset of parameters is a sound conservative policy. \[D:thm:overmodel-diagnostic; R:\[S\]\]

**2. Heuristic selection as weakened-guarantee mode.** Under \[S+ETH\], exact global minimization can be exponentially costly in the worst case (Theorem [\[thm:cost-asymmetry-eth\]](#thm:cost-asymmetry-eth){reference-type="ref" reference="thm:cost-asymmetry-eth"}); methods such as AIC/BIC/cross-validation therefore fit the "weaken guarantees" branch of Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}. \[D:thm:cost-asymmetry-eth; R:\[S+ETH\]\]

**3. Full-parameter inclusion as an $O(n)$ upper-bound strategy.** Under \[S+ETH\], if exact minimization is unresolved, including all $n$ parameters incurs linear maintenance overhead while avoiding false irrelevance claims. \[D:thm:cost-asymmetry-eth; R:\[S+ETH\]\]

**4. Irrationality outside attempted-competence-failure conditions.** If the active regime admits exact competence (tractable structural-access conditions or exact relevance identifiability), or if exact competence was never actually attempted, continued over-specification is not justified by hardness and is irrational relative to the stated objective. \[D:prop:attempted-competence-matrix, thm:tractable; R:\[tractable active regime\]\]

These corollaries are direct consequences of the hardness/tractability landscape: over-specification is an attempted-competence-failure policy, not a default optimum. To move beyond it, one must either shift to tractable regimes from Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} or adopt explicit approximation commitments. \[D:prop:attempted-competence-matrix, thm:tractable; R:\[regime-typed\]\]

[^1]: Naive subset enumeration still gives an intuitive baseline of $O(2^n)$ checks, but that is an algorithmic upper bound; the theorem below uses ETH for the lower-bound argument.


# Dominance Theorems for Hardness Placement {#sec:implications}

Regime for this section: the mechanized Boolean-coordinate model \[S_bool\] plus the architecture cost model defined below.

## Over-Specification as Diagnostic Signal

::: corollary
[]{#cor:overmodel-diagnostic-implication label="cor:overmodel-diagnostic-implication"} In the mechanized Boolean-coordinate model, if a coordinate is relevant and omitted from a candidate set $I$, then $I$ is not sufficient.
:::

::: proof
*Proof.* This is the contrapositive of `Sigma2PHardness.sufficient_iff_relevant_subset`. ◻
:::

::: corollary
[]{#cor:exact-identifiability label="cor:exact-identifiability"} In the mechanized Boolean-coordinate model, for any candidate set $I$: $$I \text{ is exactly relevance-identifying}
\iff
\bigl(I \text{ is sufficient and } I \subseteq R_{\mathrm{rel}}\bigr),$$ where $R_{\mathrm{rel}}$ is the full relevant-coordinate set.
:::

::: proof
*Proof.* This is exactly `Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`, with $R_{\mathrm{rel}}=\texttt{relevantFinset}$. ◻
:::

::: remark
[]{#rem:overmodel-conditional label="rem:overmodel-conditional"} In this paper's formal typing, over-specification is rational only under attempted competence failure: exact relevance competence is unavailable in the active regime *after* an attempted exact procedure, and integrity forbids uncertified exclusion (Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"}; Section [\[sec:engineering-justification\]](#sec:engineering-justification){reference-type="ref" reference="sec:engineering-justification"}). \[D:prop:attempted-competence-matrix; R:\[R=active declared regime\]\] Once exact competence is available in the active regime (Corollaries [\[cor:practice-bounded\]](#cor:practice-bounded){reference-type="ref" reference="cor:practice-bounded"}--[\[cor:practice-tree\]](#cor:practice-tree){reference-type="ref" reference="cor:practice-tree"} together with Corollary [\[cor:exact-identifiability\]](#cor:exact-identifiability){reference-type="ref" reference="cor:exact-identifiability"}), persistent over-specification is irrational for the same objective (verified total-cost minimization), because excluded coordinates can be certified irrelevant. \[D:prop:attempted-competence-matrix, thm:tractable; R:\[tractable active regime\]\]
:::

## Architectural Decision Quotient

::: definition
For a software system with configuration space $S$ and behavior space $B$: $$\text{ADQ}(I) = \frac{|\{b \in B : b \text{ achievable with some } s \text{ where } s_I \text{ fixed}\}|}{|B|}$$
:::

::: proposition
[]{#prop:adq-ordering label="prop:adq-ordering"} For coordinate sets $I,J$ in the same system, if $\mathrm{ADQ}(I) < \mathrm{ADQ}(J)$, then fixing $I$ leaves a strictly smaller achievable-behavior set than fixing $J$.
:::

::: proof
*Proof.* The denominator $|B|$ is shared. Thus $\mathrm{ADQ}(I) < \mathrm{ADQ}(J)$ is equivalent to a strict inequality between the corresponding achievable-behavior set cardinalities. ◻
:::

## Corollaries for Practice

::: corollary
[]{#cor:practice-diagnostic label="cor:practice-diagnostic"} In the mechanized Boolean-coordinate model, existence of a sufficient set of size at most $k$ is equivalent to the relevance set having cardinality at most $k$.
:::

::: proof
*Proof.* By `Sigma2PHardness.min_sufficient_set_iff_relevant_card`, sufficiency of size $\le k$ is equivalent to a relevance-cardinality bound $\le k$ in the Boolean-coordinate model. ◻
:::

::: corollary
[]{#cor:practice-bounded label="cor:practice-bounded"} When the bounded-action or explicit-state conditions of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} hold, minimal modeling can be solved in polynomial time in the stated input size.
:::

::: proof
*Proof.* This is the bounded-regime branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as `sufficiency_poly_bounded_actions`. ◻
:::

::: corollary
[]{#cor:practice-structured label="cor:practice-structured"} When utility is separable with explicit factors, sufficiency checking is polynomial in the explicit-state regime.
:::

::: proof
*Proof.* This is the separable-utility branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as `sufficiency_poly_separable`. ◻
:::

::: corollary
[]{#cor:practice-tree label="cor:practice-tree"} When utility factors form a tree structure with explicit local factors, sufficiency checking is polynomial in the explicit-state regime.
:::

::: proof
*Proof.* This is the tree-factor branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as `sufficiency_poly_tree_structured`. ◻
:::

::: corollary
[]{#cor:practice-unstructured label="cor:practice-unstructured"} There is a machine-checked family of reduction instances where, for non-tautological source formulas, every coordinate is relevant ($k^*=n$), exhibiting worst-case boundary complexity.
:::

::: proof
*Proof.* The strengthened reduction proves that non-tautological source formulas induce instances where every coordinate is relevant; this is mechanized as `all_coords_relevant_of_not_tautology`. ◻
:::

## Hardness Distribution: Right Place vs Wrong Place {#sec:hardness-distribution}

::: definition
[]{#def:hardness-distribution label="def:hardness-distribution"} Let $P$ be a problem family under the succinct encoding of Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}. In this section, baseline hardness $H(P;n)$ denotes worst-case computational step complexity on instances with $n$ coordinates (equivalently, as a function of succinct input length $L$) in the fixed encoding regime. A *solution architecture* $S$ partitions this baseline hardness into:

-   $H_{\text{central}}(S)$: hardness paid once, at design time or in a shared component

-   $H_{\text{distributed}}(S)$: hardness paid per use site

For $n$ use sites, total realized hardness is: $$H_{\text{total}}(S) = H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)$$
:::

::: proposition
[]{#prop:hardness-conservation label="prop:hardness-conservation"} For any problem family $P$ measured by $H(P;n)$ above, any solution architecture $S$ and any number of use sites $n \ge 1$, if $H_{\text{total}}(S)$ is measured in the same worst-case step units over the same input family, then: $$H_{\text{total}}(S) = H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S) \geq H(P;n).$$ For SUFFICIENCY-CHECK, Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} provides the baseline on the hard succinct family: $H(\text{SUFFICIENCY-CHECK};n)=2^{\Omega(n)}$ under ETH.
:::

::: proof
*Proof.* By definition, $H(P;n)$ is a worst-case lower bound for correct solutions in this encoding regime and cost metric. Any such solution architecture decomposes total realized work as $H_{\text{central}} + n\cdot H_{\text{distributed}}$, so that total cannot fall below the baseline. ◻
:::

::: definition
[]{#def:hardness-efficiency label="def:hardness-efficiency"} The *hardness efficiency* of solution $S$ with $n$ use sites is: $$\eta(S, n) = \frac{H_{\text{central}}(S)}{H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)}$$
:::

::: proposition
[]{#prop:hardness-efficiency-interpretation label="prop:hardness-efficiency-interpretation"} For fixed $n$ and positive total hardness, larger $\eta(S,n)$ is equivalent to a larger central share of realized hardness.
:::

::: proof
*Proof.* From Definition [\[def:hardness-efficiency\]](#def:hardness-efficiency){reference-type="ref" reference="def:hardness-efficiency"}, $\eta(S,n)$ is exactly the fraction of total realized hardness paid centrally. ◻
:::

::: definition
[]{#def:right-wrong-placement label="def:right-wrong-placement"} For a solution architecture $S$ in this linear model: $$\text{right hardness} \iff H_{\mathrm{distributed}}(S)=0,\qquad
\text{wrong hardness} \iff H_{\mathrm{distributed}}(S)>0.$$
:::

::: theorem
[]{#thm:centralization-dominance label="thm:centralization-dominance"} Let $S_{\mathrm{right}}, S_{\mathrm{wrong}}$ be architectures over the same problem family with $$H_{\mathrm{distributed}}(S_{\mathrm{right}})=0,\quad
H_{\mathrm{central}}(S_{\mathrm{right}})>0,\quad
H_{\mathrm{distributed}}(S_{\mathrm{wrong}})>0,$$ and let $n > \max\!\bigl(1, H_{\mathrm{central}}(S_{\mathrm{right}})\bigr)$. Then:

1.  Lower total realized hardness: $$H_{\text{total}}(S_{\mathrm{right}}) < H_{\text{total}}(S_{\mathrm{wrong}})$$

2.  Fewer error sites: errors in centralized components affect 1 location; errors in distributed components affect $n$ locations

3.  Quantified leverage: moving one unit of work from distributed to central saves exactly $n-1$ units of total realized hardness
:::

::: proof
*Proof.* (1) and (2) are exactly the bundled theorem `HardnessDistribution.centralization_dominance_bundle`. (3) is exactly `HardnessDistribution.centralization_step_saves_n_minus_one`. ◻
:::

::: corollary
[]{#cor:right-wrong-hardness label="cor:right-wrong-hardness"} In the linear model, a right-hardness architecture strictly dominates a wrong-hardness architecture once use-site count exceeds central one-time hardness. Formally, for architectures $S_{\mathrm{right}}, S_{\mathrm{wrong}}$ over the same problem family, if $S_{\mathrm{right}}$ has right hardness, $S_{\mathrm{wrong}}$ has wrong hardness, and $n > H_{\mathrm{central}}(S_{\mathrm{right}})$, then $$H_{\mathrm{central}}(S_{\mathrm{right}}) + n\,H_{\mathrm{distributed}}(S_{\mathrm{right}})
<
H_{\mathrm{central}}(S_{\mathrm{wrong}}) + n\,H_{\mathrm{distributed}}(S_{\mathrm{wrong}}).$$
:::

::: proof
*Proof.* This is the mechanized theorem `HardnessDistribution.right_dominates_wrong`. ◻
:::

::: proposition
[]{#prop:dominance-modes label="prop:dominance-modes"} This section uses two linear-model dominance modes plus generalized nonlinear dominance and boundary modes:

1.  **Strict threshold dominance:** Corollary [\[cor:right-wrong-hardness\]](#cor:right-wrong-hardness){reference-type="ref" reference="cor:right-wrong-hardness"} gives strict inequality once $n > H_{\mathrm{central}}(S_{\mathrm{right}})$.

2.  **Global weak dominance:** under the decomposition identity used in `HardnessDistribution.centralized_higher_leverage`, centralized hardness placement is never worse for all $n\ge 1$.

3.  **Generalized nonlinear dominance:** under bounded-vs-growing site-cost assumptions (Theorem [\[thm:generalized-dominance\]](#thm:generalized-dominance){reference-type="ref" reference="thm:generalized-dominance"}), right placement strictly dominates beyond a finite threshold without assuming linear per-site cost.

4.  **Generalized boundary mode:** without those growth-separation assumptions, strict dominance is not guaranteed (Proposition [\[prop:generalized-assumption-boundary\]](#prop:generalized-assumption-boundary){reference-type="ref" reference="prop:generalized-assumption-boundary"}).
:::

::: proof
*Proof.* Part (1) is Corollary [\[cor:right-wrong-hardness\]](#cor:right-wrong-hardness){reference-type="ref" reference="cor:right-wrong-hardness"}. Part (2) is exactly `HardnessDistribution.centralized_higher_leverage`. Part (3) is Theorem [\[thm:generalized-dominance\]](#thm:generalized-dominance){reference-type="ref" reference="thm:generalized-dominance"}. Part (4) is Proposition [\[prop:generalized-assumption-boundary\]](#prop:generalized-assumption-boundary){reference-type="ref" reference="prop:generalized-assumption-boundary"}. ◻
:::

**Illustrative Instantiation (Type Systems).** Consider a capability $C$ (e.g., provenance tracking) with one-time central cost $H_{\text{central}}$ and per-site manual cost $H_{\text{distributed}}$:

::: center
  **Approach**                  $H_{\text{central}}$     $H_{\text{distributed}}$
  ---------------------------- ----------------------- -----------------------------
  Native type system support    High (learning cost)    Low (type checker enforces)
  Manual implementation         Low (no new concepts)   High (reimplement per site)
:::

The table is schematic; the formal statement is Corollary [\[cor:type-system-threshold\]](#cor:type-system-threshold){reference-type="ref" reference="cor:type-system-threshold"}.

::: corollary
[]{#cor:type-system-threshold label="cor:type-system-threshold"} For the formal native-vs-manual architecture instance, native support has lower total realized cost for all $$n > H_{\mathrm{baseline}}(P),$$ where $H_{\mathrm{baseline}}(P)$ corresponds to the Lean identifier `intrinsicDOF`(P) in module `HardnessDistribution`.
:::

::: proof
*Proof.* Immediate from `HardnessDistribution.native_dominates_manual`. ◻
:::

## Extension: Non-Additive Site-Cost Models {#sec:nonadditive-site-costs}

::: definition
[]{#def:generalized-site-accumulation label="def:generalized-site-accumulation"} Let $C_S : \mathbb{N} \to \mathbb{N}$ be a per-site accumulation function for architecture $S$. Define generalized total realized hardness by $$H_{\text{total}}^{\mathrm{gen}}(S,n) = H_{\text{central}}(S) + C_S(n).$$
:::

::: definition
[]{#def:eventual-saturation label="def:eventual-saturation"} A cost function $f : \mathbb{N}\to\mathbb{N}$ is *eventually saturating* if there exists $N$ such that for all $n\ge N$, $f(n)=f(N)$.
:::

::: theorem
[]{#thm:generalized-dominance label="thm:generalized-dominance"} Let $$H_{\text{total}}^{\mathrm{gen}}(S,n)=H_{\text{central}}(S)+C_S(n).$$ For two architectures $S_{\mathrm{right}},S_{\mathrm{wrong}}$, suppose there exists $B\in\mathbb{N}$ such that:

1.  $C_{S_{\mathrm{right}}}(m)\le B$ for all $m$ (bounded right-side per-site accumulation),

2.  $m \le C_{S_{\mathrm{wrong}}}(m)$ for all $m$ (identity-lower-bounded wrong-side growth).

Then for every $$n > H_{\text{central}}(S_{\mathrm{right}})+B,$$ one has $$H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{right}},n)
<
H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{wrong}},n).$$
:::

::: proof
*Proof.* This is exactly the mechanized theorem `HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`. ◻
:::

::: corollary
[]{#cor:generalized-eventual-dominance label="cor:generalized-eventual-dominance"} If condition (1) above holds and there exists $N$ such that condition (2) holds for all $m\ge N$, then there exists $N_0$ such that for all $n\ge N_0$, $$H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{right}},n)
<
H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{wrong}},n).$$
:::

::: proof
*Proof.* Immediate from `HardnessDistribution.generalized_right_eventually_dominates_wrong`. ◻
:::

::: proposition
[]{#prop:generalized-assumption-boundary label="prop:generalized-assumption-boundary"} In the generalized model, strict right-vs-wrong dominance is not unconditional. There are explicit counterexamples:

1.  If wrong-side growth lower bounds are dropped, right-side strict dominance can fail for all $n$.

2.  If right-side boundedness is dropped, strict dominance can fail for all $n$ even when wrong-side growth is linear.
:::

::: proof
*Proof.* This is exactly the pair of mechanized boundary theorems listed above. ◻
:::

::: theorem
[]{#thm:linear-saturation-iff-zero label="thm:linear-saturation-iff-zero"} In the linear model of this section, $$H_{\text{total}}(S,n)=H_{\text{central}}(S)+n\cdot H_{\text{distributed}}(S),$$ the function $n\mapsto H_{\text{total}}(S,n)$ is eventually saturating if and only if $H_{\text{distributed}}(S)=0$.
:::

::: proof
*Proof.* This is exactly the mechanized equivalence theorem above. ◻
:::

::: theorem
[]{#thm:generalized-saturation-possible label="thm:generalized-saturation-possible"} There exists a generalized site-cost model with eventual saturation. In particular, for $$C_K(n)=\begin{cases}
n, & n\le K\\
K, & n>K,
\end{cases}$$ both $C_K$ and $n\mapsto H_{\text{central}}+C_K(n)$ are eventually saturating.
:::

::: proof
*Proof.* This is the explicit construction mechanized in Lean. ◻
:::

::: corollary
[]{#cor:linear-positive-no-saturation label="cor:linear-positive-no-saturation"} No positive-slope linear per-site model can represent the saturating family above for all $n$.
:::

::: proof
*Proof.* This follows from the mechanized theorem that any linear representation of the saturating family must have zero slope. ◻
:::

#### Mechanized strengthening reference.

The strengthened all-coordinates-relevant reduction is presented in Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} ("Mechanized strengthening") and formalized in `Reduction_AllCoords.lean` via `all_coords_relevant_of_not_tautology`.

The next section develops the major practical consequence of this framework: the Simplicity Tax Theorem.


# Conservation Law for Decision-Relevant Coordinates {#sec:simplicity-tax}

The load-bearing fact in this section is not the set identity itself; it is the difficulty of shrinking the required set $R(P)$ in the first place. By Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} (and Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} for minimization), exact relevance identification is intractable in the worst case under succinct encoding. The identities below therefore quantify how unresolved relevance is redistributed between central and per-site work.

::: definition
Let $R(P)$ be the required dimensions (those affecting $\operatorname{Opt}$) and $A(M)$ the dimensions model $M$ handles natively. The *expressive gap* is $\text{Gap}(M,P) = R(P) \setminus A(M)$.
:::

::: definition
[]{#def:simplicity-tax label="def:simplicity-tax"} The *simplicity tax* is the size of the expressive gap: $$\text{SimplicityTax}(M,P) := |\text{Gap}(M,P)|.$$
:::

::: theorem
[]{#thm:tax-conservation label="thm:tax-conservation"} $|\text{Gap}(M, P)| + |R(P) \cap A(M)| = |R(P)|$. The total cannot be reduced---only redistributed between "handled natively" and "handled externally."
:::

::: proof
*Proof.* In the finite-coordinate model this is the exact set-cardinality identity $$|R\setminus A| + |R\cap A| = |R|,$$ formalized as `HardnessDistribution.gap_conservation_card`. ◻
:::

::: remark
The algebraic identity in Theorem [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"} is elementary. Its force comes from upstream hardness: reducing $|R(P)|$ by exact relevance minimization is worst-case intractable under the succinct encoding, so redistribution is often the only tractable lever available.
:::

::: theorem
[]{#thm:tax-grows label="thm:tax-grows"} For $n$ decision sites: $$\text{TotalExternalWork} = n \times \text{SimplicityTax}(M, P).$$
:::

::: proof
*Proof.* This is by definition of per-site externalization and is mechanized as `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`. ◻
:::

::: theorem
[]{#thm:amortization label="thm:amortization"} Let $H_{\text{central}}$ be the one-time cost of using a complete model. There exists $$n^* = \left\lfloor \frac{H_{\text{central}}}{\text{SimplicityTax}(M,P)} \right\rfloor$$ such that for $n > n^*$, the complete model has lower total cost.
:::

::: proof
*Proof.* For positive per-site tax, the threshold inequality $$n > \left\lfloor \frac{H_{\text{central}}}{\text{SimplicityTax}} \right\rfloor
\implies
H_{\text{central}} < n\cdot \text{SimplicityTax}$$ is mechanized as `HardnessDistribution.complete_model_dominates_after_threshold`. ◻
:::

::: corollary
[]{#cor:gap-externalization label="cor:gap-externalization"} If $\text{Gap}(M,P)\neq\emptyset$, then external handling cost scales linearly with the number of decision sites.
:::

::: proof
*Proof.* The exact linear form is `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`. When the gap is nonempty (positive tax), monotone growth with $n$ is `HardnessDistribution.simplicityTax_grows`. ◻
:::

::: corollary
[]{#cor:gap-minimization-hard label="cor:gap-minimization-hard"} For mechanized Boolean-coordinate instances, "there exists a sufficient set of size at most $k$" is equivalent to "the relevant-coordinate set has cardinality at most $k$."
:::

::: proof
*Proof.* This is `Sigma2PHardness.min_sufficient_set_iff_relevant_card`. ◻
:::

Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} provides theorem statements and module paths for the corresponding Lean formalization.


# Related Work {#sec:related}

## Computational Decision Theory

The complexity of decision-making has been studied extensively. Papadimitriou [@papadimitriou1994complexity] established foundational results on the complexity of game-theoretic solution concepts. Our work extends this to the meta-question of identifying relevant information. For a modern treatment of complexity classes, see Arora and Barak [@arora2009computational].

#### Closest prior work and novelty.

Closest to our contribution is the feature-selection/model-selection hardness literature, which proves NP-hardness and inapproximability for predictive subset selection [@blum1997selection; @amaldi1998complexity]. Our contribution is stronger on two axes not provided by those works: (i) machine-checked reductions (TAUTOLOGY and $\exists\forall$-SAT mappings with explicit polynomial bounds), and (ii) a complete hardness/tractability landscape for decision relevance under explicit encoding assumptions. We study decision relevance rather than predictive compression, and we formalize the core reductions in Lean 4 rather than leaving them only on paper.

## Succinct Representations and Regime Separation

Representation-sensitive complexity is established in planning and decision-process theory: classical and compactly represented MDP/planning problems exhibit sharp complexity shifts under different input models [@papadimitriou1987mdp; @mundhenk2000mdp; @littman1998probplanning]. Our explicit-vs-succinct separation aligns with this broader principle.

The distinction in this paper is the object and scope of the classification: we classify *decision relevance* (sufficiency, anchor sufficiency, and minimum sufficient sets) for a fixed decision relation, with theorem-level regime typing and mechanized reduction chains.

## Oracle and Query-Access Lower Bounds

Query-access lower bounds are a standard source of computational hardness transfer [@dobzinski2012query]. Our `[Q_fin]` and `[Q_bool]` results are in this tradition, but specialized to the same sufficiency predicate used throughout the paper: they establish access-obstruction lower bounds while keeping the underlying decision relation fixed across regimes.

## Feature Selection

In machine learning, feature selection asks which input features are relevant for prediction. This is known to be NP-hard in general [@blum1997selection]. Our results show the decision-theoretic analog is coNP-complete for both checking and minimization.

## Value of Information

The value of information (VOI) framework [@howard1966information] quantifies the maximum rational payment for information. Our work addresses a different question: not the *value* of information, but the *complexity* of identifying which information has value.

## Model Selection

Statistical model selection (AIC [@akaike1974new], BIC [@schwarz1978estimating], cross-validation [@stone1974cross]) provides practical heuristics for choosing among models. Our results formalize the regime-level reason heuristic selection appears: without added structural assumptions, exact optimal model selection inherits worst-case intractability, so heuristic methods implement explicit weakened-guarantee policies for unresolved structure.

## Certifying Outputs and Proof-Carrying Claims

Our integrity layer matches the certifying-algorithms pattern: algorithms emit candidate outputs together with certificates that can be checked quickly, separating *producing* claims from *verifying* claims [@mcconnell2010certifying]. In this paper, Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"} is exactly that soundness discipline.

At the systems level, this is the same architecture as proof-carrying code: a producer ships evidence and a consumer runs a small checker before accepting the claim [@necula1997proof]. Our competence definition adds the regime-specific coverage/resource requirement that certifying soundness alone does not provide.

The feasibility qualifier in Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"} also aligns with bounded-rationality normativity: what agents *should* do is constrained by what is computationally feasible under the declared resource model [@sep_bounded_rationality]. \[D:prop:integrity-competence-separation; R:\[R=active declared regime\]\]

#### Three-axis integration.

To our knowledge, prior work treats these pillars separately: representation-sensitive hardness, query-access lower bounds, and certifying soundness disciplines. This paper integrates all three for the same decision-relevance object in one regime-typed and machine-checked framework.

## Extended Bibliographic Coverage Map

To support the grand-unification scope, we explicitly anchor additional adjacent literatures across formal methods, programming languages, information theory, optimization, and decision analysis. The following citations are included as a structured coverage map rather than as theorem-local dependencies.

#### Coverage tranche 1.

[@moura2021lean4; @cook1971complexity; @karp1972reducibility; @stockmeyer1976polynomial; @impagliazzo2001complexity; @savage1954foundations; @raiffa1961applied; @pearl1988probabilistic; @koller2009probabilistic; @chickering2004large; @teyssier2012ordering; @nipkow2014concrete; @cook2018complexity; @fisher1922mathematical; @lehmann1950completeness; @pearl2009causality; @spirtes2000causation; @shpitser2006identification].

#### Coverage tranche 2.

[@rissanen1978modeling; @grunwald2007minimum; @li2008introduction; @sobol2001global; @guyon2003introduction; @forster2019verified; @kunze2019formal; @nipkow2002isabelle; @haslbeck2021verified; @mathlib2020; @lipton2009np; @feige1998threshold; @cardelli1988semantics; @malayeri2008integrating; @malayeri2009cz; @abdelgawad2014noop; @abdelgawad2016nominal; @liskov1994behavioral].

#### Coverage tranche 3.

[@barrett1996monotonic; @cook1990inheritance; @gil2008whiteoak; @siek2006gradual; @veldhuizen2006tradeoffs; @damasevicius2010complexity; @pierce2002types; @wadler1990linear; @blum1967machine; @pep544; @pep484; @pythonBuiltinsHasattr; @bierman2014typescript; @tsHandbookTypeCompatibility; @tsIssue202; @tsPR33038; @jlsErasure; @goSpec].

#### Coverage tranche 4.

[@mdnPrototypeChain; @chugh2012nested; @systemDArxiv; @lamaison2012duck; @blum1967size; @damasevicius2010metrics; @ocamlObjectsRowVars; @abadi1996theory; @reynolds1983types; @malayeri2009esop; @openhcs2025; @openhcsPR44; @openhcsLeanProofs; @paper2_ssot; @gamma1994design; @boehm1981software; @nasa2010error; @Shannon1948].

#### Coverage tranche 5.

[@ahlswede1989identification; @CoverThomas2006; @Kolmogorov1965; @Welsh1976; @Pierce2002; @Cardelli1985; @Structural2014; @Lean2015; @Tishby2000; @Grunwald2007; @LiVitanyi2008; @PythonDocs; @CPythonDocs; @JavaDocs; @TypeScriptDocs; @RustDocs; @shannon1959coding; @berger1971rate].

#### Coverage tranche 6.

[@cousot1977abstract; @buhrman2002complexity; @JVMSpec; @RustTraitObjects; @DNABarcoding; @ISBN; @Codd1990; @ahlswede1989identification2; @hanverdu1993generalization; @steinberg1998identification; @csiszar2011information; @blahut1972computation; @gray1998quantization; @blau2019rethinking; @burnashev1976data; @wolfowitz1961coding; @korner1973coding; @witsenhausen1976zero].

#### Coverage tranche 7.

[@orlitsky1991worst; @hunt1999pragmatic].


# Conclusion

## Methodology and Disclosure {#methodology-and-disclosure .unnumbered}

**Role of LLMs in this work.** This paper was developed through human-AI collaboration. The author provided the core intuitions---the connection between decision-relevance and computational complexity, the conjecture that SUFFICIENCY-CHECK is coNP-complete, and the insight that the $\Sigma_{2}^{P}$ structure collapses for MINIMUM-SUFFICIENT-SET. Large language models (Claude, GPT-4) served as implementation partners for proof drafting, Lean formalization, and LaTeX generation.

The Lean 4 proofs were iteratively refined: the author specified the target statements, the LLM proposed proof strategies, and the Lean compiler served as the arbiter of correctness. The complexity-theoretic reductions required careful human oversight to ensure the polynomial bounds were correctly established.

**What the author contributed:** The problem formulations (SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, ANCHOR-SUFFICIENCY), the hardness conjectures, the tractability conditions, and the connection to over-modeling in engineering practice.

**What LLMs contributed:** LaTeX drafting, Lean tactic exploration, reduction construction assistance, and prose refinement.

The proofs are machine-checked; their validity is independent of generation method. We disclose this methodology in the interest of academic transparency.

::: center

----------------------------------------------------------------------------------------------------
:::

## Summary of Results {#summary-of-results .unnumbered}

This paper establishes the computational complexity of coordinate sufficiency problems:

-   **SUFFICIENCY-CHECK** is coNP-complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"})

-   **MINIMUM-SUFFICIENT-SET** is coNP-complete (Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"})

-   **ANCHOR-SUFFICIENCY** is $\Sigma_{2}^{P}$-complete (Theorem [\[thm:anchor-sigma2p\]](#thm:anchor-sigma2p){reference-type="ref" reference="thm:anchor-sigma2p"})

-   An encoding-regime separation contrasts explicit-state polynomial-time (polynomial in $|S|$) with a succinct worst-case ETH lower bound witnessed by a hard family with $k^*=n$ (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"})

-   Full intermediate query-access lower bounds are formalized as a finite-state Opt-oracle core ($\Omega(|S|)$, Boolean instantiation $\Omega(2^n)$) plus Boolean-interface refinements for value-entry and state-batch access, with explicit subproblem-to-full transfer, weighted randomized robustness, and oracle-lattice transfer/strictness closures (Propositions [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"}--[\[prop:oracle-lattice-strict\]](#prop:oracle-lattice-strict){reference-type="ref" reference="prop:oracle-lattice-strict"})

-   Tractable subcases exist for explicit-state encoding, separable utility, and tree-structured utility with explicit local factors (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"})

These results place the problem of identifying decision-relevant coordinates at the first and second levels of the polynomial hierarchy.

Beyond classification, the paper contributes a formal claim-typing framework (Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"}): structural complexity is a property of the fixed decision question, while representational hardness is regime-conditional access cost. This is why encoding-regime changes can move practical hardness without changing the underlying semantics.

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} for proof listings). The formalization verifies that the TAUTOLOGY reduction correctly maps tautologies to sufficient coordinate sets; complexity classifications (coNP-completeness, $\Sigma_{2}^{P}$-completeness) follow by composition with standard complexity-theoretic results (TAUTOLOGY is coNP-complete, $\exists\forall$-SAT is $\Sigma_{2}^{P}$-complete). The strengthened gadget showing that non-tautologies yield instances with *all coordinates relevant* is also formalized.

## Complexity Characterization {#complexity-characterization .unnumbered}

The results provide precise complexity characterizations within the formal model:

1.  **Exact bounds.** SUFFICIENCY-CHECK is coNP-complete---both coNP-hard and in coNP.

2.  **Constructive reductions.** The reductions from TAUTOLOGY and $\exists\forall$-SAT are explicit and machine-checked.

3.  **Encoding-regime separation.** Under \[E\], SUFFICIENCY-CHECK is polynomial in $|S|$. Under \[S+ETH\], there exist succinct worst-case instances (with $k^*=n$) requiring $2^{\Omega(n)}$ time. Under \[Q_fin\], the Opt-oracle core has $\Omega(|S|)$ worst-case query complexity (Boolean instantiation $\Omega(2^n)$), and under \[Q_bool\] the value-entry/state-batch refinements preserve the obstruction with weighted-cost transfer closures.

## The Complexity Redistribution Corollary {#the-complexity-redistribution-corollary .unnumbered}

Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} develops a quantitative consequence: when a problem requires $k$ dimensions and a model handles only $j < k$ natively, the remaining $k - j$ dimensions must be handled externally at each decision site. For $n$ sites, total external work is $(k-j) \times n$. \[D:thm:tax-grows; R:\[linear cost model\]\]

The set identity is elementary; its operational content comes from composition with the hardness results on exact relevance minimization. This redistribution corollary is formalized in Lean 4 (`HardnessDistribution.lean`), proving:

-   Redistribution identity: complexity burden cannot be eliminated by omission, only moved between native handling and external handling

-   Dominance: complete models have lower total work than incomplete models

-   Amortization: there exists a threshold $n^*$ beyond which higher-dimensional models have lower total cost

## Open Questions {#open-questions .unnumbered}

The landscape above is complete for the static sufficiency class under C1--C4 and the declared regimes; the items below are adjacent-class extensions or secondary refinements. Several questions remain for future work:

-   **Fixed-parameter tractability (primary):** Is SUFFICIENCY-CHECK FPT when parameterized by the minimal sufficient-set size $k^*$, or is it W\[2\]-hard under this parameterization?

-   **Sequential/stochastic bridge extension:** Characterize the exact frontier where adjacent sequential objectives reduce to the static class via Proposition [\[prop:one-step-bridge\]](#prop:one-step-bridge){reference-type="ref" reference="prop:one-step-bridge"}, and where genuinely new complexity objects (e.g., horizon/sample/regret complexity) must replace the present coNP/$\Sigma_2^P$ analysis.

-   **Average-case complexity:** What is the complexity under natural distributions on decision problems?

-   **Learning cost formalization:** Can central cost $H_{\text{central}}$ be formalized as the rank of a concept matroid, making the amortization threshold precisely computable?

## Practical Corollaries {#practical-corollaries .unnumbered}

The practical corollaries are regime-indexed and theorem-indexed:

-   **\[E\] and structured regimes:** polynomial-time exact procedures exist (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

-   **\[Q_fin\]/\[Q_bool\] query-access lower bounds:** worst-case Opt-oracle complexity is $\Omega(|S|)$ in the finite-state core (Boolean instantiation $\Omega(2^n)$), and value-entry/state-batch interfaces satisfy the same obstruction in the mechanized Boolean refinement (Propositions [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"}--[\[prop:oracle-lattice-strict\]](#prop:oracle-lattice-strict){reference-type="ref" reference="prop:oracle-lattice-strict"}), with randomized weighted robustness and oracle-lattice closures.

-   **\[S+ETH\] hard families:** exact minimization inherits exponential worst-case cost (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} together with Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}).

-   **\[S_bool\] mechanized criterion:** minimization reduces to relevance-cardinality constraints (Corollary [\[cor:practice-diagnostic\]](#cor:practice-diagnostic){reference-type="ref" reference="cor:practice-diagnostic"}).

-   **Redistribution consequences:** omitted native coverage externalizes work with explicit growth/amortization laws (Theorems [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"}--[\[thm:amortization\]](#thm:amortization){reference-type="ref" reference="thm:amortization"}).

Hence the design choice is typed: enforce a tractable regime, or adopt weakened guarantees with explicit verification boundaries. \[D:thm:tractable, thm:dichotomy; R:\[regime-typed\]\] Equivalently, over-specification is a conditional attempted-competence-failure policy in this framework; once exact competence is available in the active regime (or no attempted exact competence was made), persistent over-specification is irrational for the same verified-cost objective. \[D:prop:attempted-competence-matrix; R:\[R=active declared regime\]\] By Proposition [\[prop:attempted-competence-matrix\]](#prop:attempted-competence-matrix){reference-type="ref" reference="prop:attempted-competence-matrix"}, this is not a close call: in the integrity-preserving matrix, irrational cells outnumber rational cells (3 vs 1). \[D:prop:attempted-competence-matrix; R:\[R=active declared regime\]\]


# Lean 4 Proof Listings {#app:lean}

The complete Lean 4 formalization is available in the companion artifact (Zenodo DOI listed on the title page). The mechanization consists of 8698 lines across 42 files, with 393 theorem/lemma statements.

## What Is Machine-Checked

The Lean formalization establishes:

1.  **Correctness of the TAUTOLOGY reduction:** The theorem `tautology_iff_sufficient` proves that the mapping from Boolean formulas to decision problems preserves the decision structure (accept iff the formula is a tautology).

2.  **Decision problem definitions:** Formal definitions of sufficiency, optimality, and the decision quotient.

3.  **Economic theorems:** Simplicity Tax redistribution identities and hardness distribution results.

4.  **Query-access lower-bound core:** Formalized Boolean query-model indistinguishability theorem for the full problem via the $I=\emptyset$ subproblem (`emptySufficiency_query_indistinguishable_pair`), plus obstruction-scale identities (`queryComplexityLowerBound`, `exponential_query_complexity`).

**Complexity classifications** (coNP-completeness, $\Sigma_2^P$-completeness) follow by conditional composition with standard results (e.g., TAUTOLOGY coNP-completeness and $\exists\forall$-SAT $\Sigma_2^P$-completeness), represented explicitly as hypotheses in the conditional transfer theorems listed below. The Lean proofs verify the reduction constructions and the transfer closures under those hypotheses. The assumptions themselves are unpacked by an explicit ledger projection theorem (`ClaimClosure.standard_assumption_ledger_unpack`) so dependency tracking is machine-auditable.

## Polynomial-Time Reduction Definition

We use Mathlib's Turing machine framework to define polynomial-time computability:

    /-- Polynomial-time computable function using Turing machines -/
    def PolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) 
        (f : α → β) : Prop :=
      Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

    /-- Polynomial-time many-one (Karp) reduction -/
    def ManyOneReducesPoly {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
        (A : Set α) (B : Set β) : Prop :=
      ∃ f : α → β, PolyTime ea eb f ∧ ∀ x, x ∈ A ↔ f x ∈ B

This uses the standard definition: a reduction is polynomial-time computable via Turing machines and preserves membership.

## The Main Reduction Theorem

::: theorem
The reduction from TAUTOLOGY to SUFFICIENCY-CHECK is correct:
:::

    theorem tautology_iff_sufficient (φ : Formula n) :
        φ.isTautology ↔ (reductionProblem φ).isSufficient Finset.empty

This theorem is proven by showing both directions:

-   If $\varphi$ is a tautology, then the empty coordinate set is sufficient

-   If the empty coordinate set is sufficient, then $\varphi$ is a tautology

The proof verifies that the utility construction in `reductionProblem` creates the appropriate decision structure where:

-   At reference states, `accept` is optimal with utility 1

-   At assignment states, `accept` is optimal iff $\varphi(a) = \text{true}$

## Economic Results

The hardness distribution theorems (Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"}) are fully formalized:

    theorem simplicityTax_conservation (P : SpecificationProblem)
        (S : SolutionArchitecture P) :
        S.centralDOF + simplicityTax P S ≥ P.intrinsicDOF

    theorem simplicityTax_grows (P : SpecificationProblem)
        (S : SolutionArchitecture P) (n₁ n₂ : ℕ)
        (hn : n₁ < n₂) (htax : simplicityTax P S > 0) :
        totalDOF S n₁ < totalDOF S n₂

    theorem native_dominates_manual (P : SpecificationProblem) (n : Nat)
        (hn : n > P.intrinsicDOF) :
        totalDOF (nativeTypeSystem P) n < totalDOF (manualApproach P) n

    theorem totalDOF_eventually_constant_iff_zero_distributed
        (S : SolutionArchitecture P) :
        IsEventuallyConstant (fun n => totalDOF S n) ↔ S.distributedDOF = 0

    theorem no_positive_slope_linear_represents_saturating
        (c d K : ℕ) (hd : d > 0) :
        ¬ (∀ n, c + n * d = generalizedTotalDOF c (saturatingSiteCost K) n)

**Identifier note.** Lean identifiers retain internal naming (`intrinsicDOF`, `simplicityTax_conservation`); in paper terminology these correspond to *baseline hardness* and the *redistribution lower-bound identity*, respectively.

## Complete Claim Coverage Matrix

## Claims Not Fully Mechanized

**Status:** all theorem/proposition/corollary handles in this paper now have Lean backing. Entries marked **Full (conditional)** are explicitly mechanized transfer theorems that depend on standard external complexity facts (e.g., source-class completeness or ETH assumptions), with those dependencies represented as hypotheses in Lean.

## Module Structure

-   `Basic.lean` -- Core definitions (DecisionProblem, sufficiency, optimality)

-   `Sufficiency.lean` -- Sufficiency checking algorithms and properties

-   `Reduction.lean` -- TAUTOLOGY reduction construction and correctness

-   `Hardness/ConfigReduction.lean` -- Sentinel-action configuration reduction theorem

-   `Complexity.lean` -- Polynomial-time reduction definitions using mathlib

-   `HardnessDistribution.lean` -- Simplicity Tax redistribution and amortization theorems

-   `IntegrityCompetence.lean` -- Solver integrity vs regime competence separation

-   `ClaimClosure.lean` -- Mechanized closure of paper-level bridge and diagnostic claims

-   `Tractability/` -- Bounded actions, separable utilities, tree structure

## Verification

The proofs compile with Lean 4 and contain no `sorry` placeholders. Run `lake build` in the proof directory to verify.


## Assumption Ledger (Auto)

#### Source files.

-   `DecisionQuotient/ClaimClosure.lean`

#### Assumption bundles and fields.

-   (No assumption bundles parsed.)

#### Conditional closure handles.

-   `DecisionQuotient.anchor_sigma2p_complete_conditional`

-   `DecisionQuotient.cost_asymmetry_eth_conditional`

-   `DecisionQuotient.dichotomy_conditional`

-   `DecisionQuotient.minsuff_collapse_to_conp_conditional`

-   `DecisionQuotient.minsuff_conp_complete_conditional`

-   `DecisionQuotient.sufficiency_conp_complete_conditional`

-   `DecisionQuotient.tractable_subcases_conditional`


  ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  **Paper handle**                            **Status**   **Lean support**
  ------------------------------------------- ------------ ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  `cor:exact-identifiability`                 Full         `Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`

  `cor:gap-externalization`                   Full         `HardnessDistribution.simplicityTax_grows`, `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`

  `cor:gap-minimization-hard`                 Full         `Sigma2PHardness.min_sufficient_set_iff_relevant_card`

  `cor:generalized-eventual-dominance`        Full         `HardnessDistribution.generalized_right_eventually_dominates_wrong`

  `cor:linear-positive-no-saturation`         Full         `HardnessDistribution.no_positive_slope_linear_represents_saturating`

  `cor:no-auto-minimize`                      Full         `ClaimClosure.no_auto_minimize_of_p_neq_conp`

  `cor:overmodel-diagnostic-implication`      Full         `Sigma2PHardness.sufficient_iff_relevant_subset`

  `cor:practice-bounded`                      Full         `sufficiency_poly_bounded_actions`

  `cor:practice-diagnostic`                   Full         `Sigma2PHardness.min_sufficient_set_iff_relevant_card`

  `cor:practice-structured`                   Full         `sufficiency_poly_separable`

  `cor:practice-tree`                         Full         `sufficiency_poly_tree_structured`

  `cor:practice-unstructured`                 Full         `all_coords_relevant_of_not_tautology`

  `cor:query-obstruction-bool`                Full         `ClaimClosure.query_obstruction_boolean_corollary`, `emptySufficiency_query_indistinguishable_pair`

  `cor:right-wrong-hardness`                  Full         `HardnessDistribution.right_dominates_wrong`

  `cor:type-system-threshold`                 Full         `HardnessDistribution.native_dominates_manual`

  `prop:adq-ordering`                         Full         `ClaimClosure.adq_ordering`

  `prop:attempted-competence-matrix`          Full         `IntegrityCompetence.admissible_irrational_strictly_more_than_rational`, `IntegrityCompetence.admissible_matrix_counts`, `IntegrityCompetence.overModelVerdict_rational_iff`

  `prop:bridge-failure-horizon`               Full         `ClaimClosure.horizonTwoWitness_immediate_empty_sufficient`, `ClaimClosure.horizon_gt_one_bridge_can_fail_on_sufficiency`

  `prop:bridge-failure-stochastic`            Full         `ClaimClosure.stochastic_objective_bridge_can_fail_on_sufficiency`

  `prop:bridge-failure-transition`            Full         `ClaimClosure.transition_coupled_bridge_can_fail_on_sufficiency`

  `prop:bridge-transfer-scope`                Full         `ClaimClosure.one_step_bridge`

  `prop:dominance-modes`                      Full         `HardnessDistribution.centralized_higher_leverage`

  `prop:generalized-assumption-boundary`      Full         `HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`, `HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`

  `prop:hardness-conservation`                Full         `HardnessDistribution.totalDOF_ge_intrinsic`

  `prop:hardness-efficiency-interpretation`   Full         `HardnessDistribution.hardnessEfficiency_eq_central_share`

  `prop:heuristic-reusability`                Full         `ClaimClosure.bounded_actions_detectable`, `ClaimClosure.reusable_heuristic_of_detectable`, `ClaimClosure.separable_detectable`, `ClaimClosure.tree_structure_detectable`

  `prop:integrity-competence-separation`      Full         `IntegrityCompetence.competence_implies_integrity`, `IntegrityCompetence.integrity_not_competent_of_nonempty_scope`

  `prop:integrity-resource-bound`             Full         `ClaimClosure.integrity_resource_bound_for_sufficiency`, `IntegrityCompetence.integrity_forces_abstention`, `IntegrityCompetence.integrity_resource_bound`

  `prop:minimal-relevant-equiv`               Full         `DecisionProblem.minimalSufficient_iff_relevant`, `DecisionProblem.relevantSet_is_minimal`

  `prop:one-step-bridge`                      Full         `ClaimClosure.one_step_bridge`

  `prop:oracle-lattice-strict`                Full         `const_vs_scaled_opt_view_equal`, `const_vs_scaled_value_entry_diff_at_true`

  `prop:oracle-lattice-transfer`              Full         `ClaimClosure.oracle_lattice_transfer_as_regime_simulation`, `valueEntryView_eq_of_stateBatchView_eq_on_touched`

  `prop:query-finite-state-generalization`    Full         `emptySufficiency_query_indistinguishable_pair_finite`, `spikeFinite_empty_not_sufficient`

  `prop:query-randomized-robustness`          Full         `decode_error_sum_two_labels`, `indistinguishable_pair_forces_one_error`, `indistinguishable_pair_forces_one_error_per_seed`

  `prop:query-randomized-weighted`            Full         `weighted_seed_error_identity`, `weighted_seed_half_floor`

  `prop:query-regime-obstruction`             Full         `ClaimClosure.query_obstruction_finite_state_core`, `emptySufficiency_query_indistinguishable_pair_finite`, `spikeFinite_empty_not_sufficient`

  `prop:query-state-batch-lb`                 Full         `emptySufficiency_stateBatch_indistinguishable_pair`, `stateBatchView_eq_if_hidden_untouched`

  `prop:query-subproblem-transfer`            Full         `ClaimClosure.regime_simulation_transfers_hardness`, `ClaimClosure.subproblem_hardness_lifts_to_full`, `ClaimClosure.subproblem_transfer_as_regime_simulation`

  `prop:query-tightness-full-scan`            Full         `full_query_distinguishes_const_spike_finite`

  `prop:query-value-entry-lb`                 Full         `emptySufficiency_valueEntry_indistinguishable_pair`, `touchedStates_card_le_query_card`

  `prop:query-weighted-transfer`              Full         `weightedQueryCost_ge_min_mul_card`, `weightedQueryCost_ge_min_mul_of_card_lb`

  `prop:selector-separation`                  Full         `ClaimClosure.selectorSufficient_not_implies_setSufficient`

  `prop:set-to-selector`                      Full         `DecisionProblem.sufficient_implies_selectorSufficient`

  `prop:snapshot-process-typing`              Full         `ClaimClosure.agent_transfer_licensed_iff_snapshot`, `ClaimClosure.process_bridge_failure_witness`, `ClaimClosure.snapshot_vs_process_typed_boundary`

  `prop:sufficiency-char`                     Full         `ClaimClosure.sufficiency_iff_dq_ratio`, `ClaimClosure.sufficiency_iff_projectedOptCover_eq_opt`

  `prop:zero-epsilon-competence`              Full         `IntegrityCompetence.epsilon_competence_implies_integrity`, `IntegrityCompetence.zero_epsilon_competence_iff_exact`

  `prop:zero-epsilon-reduction`               Full         `DecisionProblem.epsOpt_zero_eq_opt`, `DecisionProblem.sufficient_iff_zeroEpsilonSufficient`

  `thm:amortization`                          Full         `HardnessDistribution.complete_model_dominates_after_threshold`

  `thm:bridge-boundary-represented`           Full         `ClaimClosure.bridge_boundary_represented_family`, `ClaimClosure.bridge_failure_witness_non_one_step`, `ClaimClosure.bridge_transfer_iff_one_step_class`

  `thm:centralization-dominance`              Full         `HardnessDistribution.centralization_dominance_bundle`, `HardnessDistribution.centralization_step_saves_n_minus_one`

  `thm:config-reduction`                      Full         `ConfigReduction.config_sufficiency_iff_behavior_preserving`

  `thm:cost-asymmetry-eth`                    Full         `ClaimClosure.cost_asymmetry_eth_conditional`, `HardnessDistribution.linear_lt_exponential_plus_constant_eventually`

  `thm:dichotomy`                             Full         `ClaimClosure.dichotomy_conditional`, `ClaimClosure.explicit_state_upper_core`, `ClaimClosure.hard_family_all_coords_core`

  `thm:generalized-dominance`                 Full         `HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`

  `thm:generalized-saturation-possible`       Full         `HardnessDistribution.generalizedTotal_with_saturation_eventually_constant`, `HardnessDistribution.saturatingSiteCost_eventually_constant`

  `thm:linear-saturation-iff-zero`            Full         `HardnessDistribution.totalDOF_eventually_constant_iff_zero_distributed`

  `thm:overmodel-diagnostic`                  Full         `ClaimClosure.boundaryCharacterized_iff_exists_sufficient_subset`, `ClaimClosure.no_exact_identifier_implies_not_boundary_characterized`

  `thm:regime-coverage`                       Full         `ClaimClosure.declaredRegimeFamily_complete`, `ClaimClosure.regime_core_claim_proved`

  `thm:tax-conservation`                      Full         `HardnessDistribution.gap_conservation_card`

  `thm:tax-grows`                             Full         `HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`

  `thm:tractable`                             Full         `ClaimClosure.tractable_bounded_core`, `ClaimClosure.tractable_separable_core`, `ClaimClosure.tractable_subcases_conditional`, `ClaimClosure.tractable_tree_core`

  `thm:typed-completeness-static`             Full         `ClaimClosure.typed_static_class_completeness`
  ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

*Auto summary: mapped 62/62 theorem-level handles from inline anchors.*




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper4_decision_quotient/proofs/`
- Lines: 8698
- Theorems: 393
- `sorry` placeholders: 0
