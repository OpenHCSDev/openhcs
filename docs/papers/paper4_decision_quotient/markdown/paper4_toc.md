# Paper: Computational Complexity of Information Sufficiency

**Status**: Theory of Computing-ready | **Lean**: 11932 lines, 553 theorems

---

## Abstract

We characterize the computational complexity of *information sufficiency* as a *meta-problem*: given an arbitrary decision problem $\mathcal{D}$ with action set $A$, factored state space $S = X_1 \times \cdots \times X_n$, and utility $U: A \times S \to \mathbb{Q}$, does a candidate coordinate set $I$ carry enough information to act optimally? Formally, $I$ is *sufficient* if $s_I = s'_I \implies \operatorname{Opt}(s) = \operatorname{Opt}(s')$. Because the problems below are parameterized by an arbitrary $\mathcal{D}$, and any problem requiring a choice among alternatives under structured information instantiates the $(A, S, U)$ tuple, the complexity results apply to every problem with factored state space, not to a specific problem domain (e.g., configuration simplification where parameters are coordinates and behavior-preservation is sufficiency).

Information-theoretically, this is task-conditional compression: the target is preservation of the optimal-action map rather than full-state reconstruction. This places the framework at the interface of source coding and zero-error confusability structure [@shannon1948mathematical; @cover2006elements; @shannon1956zero; @korner1973graphs; @lovasz1979shannon], while separating short report length from certifiable exactness in the MDL/Kolmogorov sense [@rissanen1978modeling; @grunwald2007minimum; @li2008introduction].

**The landscape in the formal model:**

-   **General case:** SUFFICIENCY-CHECK is coNP-complete; ANCHOR-SUFFICIENCY is $\Sigma_{2}^{P}$-complete.

-   **Tractable cases:** Polynomial-time for bounded action sets under the explicit-state encoding; separable utilities ($U = f + g$) under any encoding; and tree-structured utility with explicit local factors.

-   **Encoding-regime separation:** Polynomial-time under the explicit-state encoding (polynomial in $|S|$). Under ETH, there exist succinctly encoded worst-case instances witnessed by a strengthened Lean-mechanized reduction gadget from the paper's SAT/TAUTOLOGY hardness spine (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}) with $k^*=n$ for which SUFFICIENCY-CHECK requires $2^{\Omega(n)}$ time.

-   **Intermediate query-access lower bounds:** In the finite-state query core, SUFFICIENCY-CHECK has worst-case Opt-oracle query complexity $\Omega(|S|)$ via indistinguishable yes/no pairs for the $I=\emptyset$ subproblem (Boolean instantiation: $\Omega(2^n)$); mechanized Boolean interface refinements show the same obstruction for value-entry and state-batch access, including finite-support randomized robustness and oracle-lattice transfer/strictness statements.

The tractable cases are stated with explicit encoding assumptions (Section [\[sec:encoding\]](#sec:encoding){reference-type="ref" reference="sec:encoding"}). Together, these results answer the question "when is decision-relevant information identifiable efficiently?" within the stated regimes. Complexity classification is a property of the encoding regime measured against a fixed decision question (Remark [\[rem:question-vs-problem\]](#rem:question-vs-problem){reference-type="ref" reference="rem:question-vs-problem"}): the same sufficiency predicate is polynomial-time under explicit-state access and worst-case exponential under succinct encoding. At the structural level, the apparent $\exists\forall$ form of MINIMUM-SUFFICIENT-SET collapses to a coNP characterization via the criterion $\text{sufficient}(I) \iff \text{Relevant} \subseteq I$. Within this regime-typed framework, under a declared objective contract, over-modeling is admissible only under integrity-preserving attempted-competence-failure conditions (roughly: after an attempted exact procedure, exact competence remains unavailable in the active regime); outside that cell, persistent over-modeling is irrational for the same objective. \[D:Pprop:attempted-competence-matrix; R:AR\] The report layer is now formally non-binary: abstention can carry a tentative guess and self-reflected confidence, while certified confidence is evidence-gated by typed admissibility; positive certified confidence implies admissibility, and exact reports without exact competence force zero certified confidence. \[D:Pprop:certified-confidence-gate, prop:abstain-guess-self-signal, prop:self-confidence-not-certification;Ccor:exact-no-competence-zero-certified; R:AR\] For progress semantics, the framework distinguishes confidence percentages from runtime witnesses: scalar step-count is always well-defined/falsifiable, while completion percentage is defined only under an explicit declared bound. \[D:Pprop:steps-run-scalar, prop:no-fraction-without-bound, prop:fraction-defined-under-bound; R:AR\] For temporal semantics, interface time is formalized as a discrete $\mathbb{N}$ index; one decision event is exactly one time-unit transition, and run length equals elapsed interface time. \[D:Pprop:time-discrete, prop:decision-unit-time, prop:run-time-accounting; R:AR\]

The contribution has two levels: (i) a complete complexity landscape for the core decision-relevant problems in the static sufficiency class defined by the model contract (coNP/$\Sigma_2^P$ completeness and tractable regimes under explicit encoding assumptions), and (ii) a formal regime-typing framework that separates structural complexity from representational hardness and yields theorem-indexed engineering corollaries.

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 (11932 lines, 553 theorem/lemma statements); complexity classifications follow by composition with standard results (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}).

**Keywords:** computational complexity, decision theory, polynomial hierarchy, tractability dichotomy, Lean 4


# Introduction {#sec:introduction}

Consider any decision problem $\mathcal{D}$ with actions $A$ and factored state space $S = X_1 \times \cdots \times X_n$. A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only coordinates in $I$ determines the optimal action: $$s_I = s'_I \implies \operatorname{Opt}(s) = \operatorname{Opt}(s')$$ This is *coordinate sufficiency*, the formalization of *information sufficiency* (whether available information determines the optimal action) over a factored state space.

In information-theoretic terms, this is a task-conditional coding problem: the object preserved by projection is the decision boundary $s \mapsto \operatorname{Opt}(s)$, not the full source state. The same object appears in classical source-coding and fidelity viewpoints [@shannon1948mathematical; @shannon1959coding; @cover2006elements; @slepian1973noiseless], and in zero-error/confusability structure where exact recoverability depends on graph constraints rather than raw description length [@shannon1956zero; @korner1973graphs; @lovasz1979shannon; @csiszar2011information]. The same separation also appears in model selection: short descriptions and certifiable adequacy are distinct [@rissanen1978modeling; @grunwald2007minimum; @li2008introduction; @blahut1972computation].

#### Compact claim-stamp notation.

We use compact provenance stamps of the form $[C:\cdots;R:\cdots]$: claim references are grouped by type ($D/P/C/T/L/R$ for Definition/Proposition/Corollary/Theorem/Lemma/Remark), and regime tags are abbreviated (for example $AR$=active declared regime, $DC$=declared contract, $CR$=declared class/regime, $Qf$=query-finite, $Qb$=query-Boolean).

SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, and ANCHOR-SUFFICIENCY are *meta-problems*: each is parameterized by an arbitrary decision problem $\mathcal{D}$ and asks a structural question about $\mathcal{D}$'s coordinate space. The complexity results therefore apply to every problem with factored state space, not to a specific problem domain. \[D:Tthm:sufficiency-conp, thm:minsuff-conp, thm:anchor-sigma2p; R:S\]

::: remark
[]{#rem:universality label="rem:universality"} The formal object of this paper is the decision-problem tuple $\mathcal{D} = (A, S, U)$: actions, factored states, utility. Within this model family, any problem requiring a choice among alternatives given structured information instantiates the tuple: the alternatives are $A$, the structured information is $S = X_1 \times \cdots \times X_n$, and the objective is $U$. Thus the qualifier "decision problem" does not narrow scope *inside the declared coordinate model*. The meta-problem results below are universal over problems representable with this coordinate structure; the $(A, S, U)$ formalism supplies the language for stating the sufficiency predicate.
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

An operational criterion follows later from the same chain: once decision-site count exceeds the amortization threshold $n^*$, avoiding structural identification is more expensive than paying the one-time centralization cost (Theorem [\[thm:amortization\]](#thm:amortization){reference-type="ref" reference="thm:amortization"}). \[D:Tthm:amortization; R:LC\]

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

6.  **Propositions [\[prop:time-discrete\]](#prop:time-discrete){reference-type="ref" reference="prop:time-discrete"}--[\[prop:substrate-unit-time\]](#prop:substrate-unit-time){reference-type="ref" reference="prop:substrate-unit-time"}:** the interface-time model is discrete, each decision event advances time by one unit, run-length equals elapsed interface time, and the unit-time law is substrate-invariant under the declared interface-consistency condition.

## Claim-Typing Theorems

1.  **Proposition [\[prop:typed-claim-admissibility\]](#prop:typed-claim-admissibility){reference-type="ref" reference="prop:typed-claim-admissibility"}:** report admissibility is typed by certificate class ($\mathsf{ABSTAIN}$, $\mathsf{EXACT}$, $\mathsf{EPSILON}(\varepsilon)$).

2.  **Proposition [\[prop:evidence-admissibility-equivalence\]](#prop:evidence-admissibility-equivalence){reference-type="ref" reference="prop:evidence-admissibility-equivalence"}:** first-class evidence-object existence is equivalent to typed report admissibility.

3.  **Propositions [\[prop:empty-sufficient-constant\]](#prop:empty-sufficient-constant){reference-type="ref" reference="prop:empty-sufficient-constant"} and [\[prop:insufficiency-counterexample\]](#prop:insufficiency-counterexample){reference-type="ref" reference="prop:insufficiency-counterexample"}:** the $I=\emptyset$ query is exactly universal constancy of the decision boundary, and non-sufficiency is exactly existence of a counterexample pair.

4.  **Proposition [\[prop:exact-requires-evidence\]](#prop:exact-requires-evidence){reference-type="ref" reference="prop:exact-requires-evidence"}:** exact admissibility is equivalent to exact evidence existence.

5.  **Proposition [\[prop:certified-confidence-gate\]](#prop:certified-confidence-gate){reference-type="ref" reference="prop:certified-confidence-gate"} and Corollary [\[cor:exact-no-competence-zero-certified\]](#cor:exact-no-competence-zero-certified){reference-type="ref" reference="cor:exact-no-competence-zero-certified"}:** certified confidence is evidence-gated; for exact reports in no-competence regimes, certified confidence must be zero.

6.  **Proposition [\[prop:no-evidence-zero-certified\]](#prop:no-evidence-zero-certified){reference-type="ref" reference="prop:no-evidence-zero-certified"}:** under signal consistency, no evidence implies zero certified confidence.

7.  **Proposition [\[prop:abstain-guess-self-signal\]](#prop:abstain-guess-self-signal){reference-type="ref" reference="prop:abstain-guess-self-signal"} and Proposition [\[prop:self-confidence-not-certification\]](#prop:self-confidence-not-certification){reference-type="ref" reference="prop:self-confidence-not-certification"}:** abstain may carry tentative guesses and self-reflected confidence, but self-confidence alone does not certify exactness.

8.  **Propositions [\[prop:steps-run-scalar\]](#prop:steps-run-scalar){reference-type="ref" reference="prop:steps-run-scalar"}, [\[prop:no-fraction-without-bound\]](#prop:no-fraction-without-bound){reference-type="ref" reference="prop:no-fraction-without-bound"}, [\[prop:fraction-defined-under-bound\]](#prop:fraction-defined-under-bound){reference-type="ref" reference="prop:fraction-defined-under-bound"}:** scalar step-count witnesses are always exact/falsifiable, while completion percentages are meaningful only under explicit declared bounds.

9.  **Theorem [\[thm:claim-integrity-meta\]](#thm:claim-integrity-meta){reference-type="ref" reference="thm:claim-integrity-meta"}:** outside declared carve-outs, admissible exact-claim policy requires explicit assumptions.

10. **Proposition [\[prop:integrity-resource-bound\]](#prop:integrity-resource-bound){reference-type="ref" reference="prop:integrity-resource-bound"}:** under non-collapse, integrity and exact competence cannot both hold universally on hardness-blocked declared regimes.

11. **Proposition [\[prop:physics-no-universal-exact\]](#prop:physics-no-universal-exact){reference-type="ref" reference="prop:physics-no-universal-exact"} and Corollary [\[cor:physics-no-universal-exact-claim\]](#cor:physics-no-universal-exact-claim){reference-type="ref" reference="cor:physics-no-universal-exact-claim"}:** schema-level consequence for declared class/regime objects and exact-report inadmissibility.

\[D:Tthm:claim-integrity-meta;Pprop:typed-claim-admissibility, prop:evidence-admissibility-equivalence, prop:empty-sufficient-constant, prop:insufficiency-counterexample, prop:exact-requires-evidence, prop:certified-confidence-gate, prop:no-evidence-zero-certified, prop:abstain-guess-self-signal, prop:self-confidence-not-certification, prop:steps-run-scalar, prop:no-fraction-without-bound, prop:fraction-defined-under-bound, prop:integrity-resource-bound, prop:physics-no-universal-exact;Ccor:exact-no-competence-zero-certified, cor:physics-no-universal-exact-claim; R:DC,AR\]

## Regime Separation Theorems

1.  **Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}:** same-question separation between explicit-state and succinct regimes (with \[S+ETH\] hard-family lower bound).

2.  **Proposition [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"}:** finite-state Opt-oracle lower bound in \[Q_fin\].

3.  **Propositions [\[prop:query-value-entry-lb\]](#prop:query-value-entry-lb){reference-type="ref" reference="prop:query-value-entry-lb"}--[\[prop:oracle-lattice-strict\]](#prop:oracle-lattice-strict){reference-type="ref" reference="prop:oracle-lattice-strict"}:** Boolean-interface refinements and transfer/strictness in \[Q_bool\].

\[D:Tthm:dichotomy;Pprop:query-regime-obstruction, prop:query-value-entry-lb, prop:query-state-batch-lb, prop:query-subproblem-transfer, prop:oracle-lattice-transfer, prop:oracle-lattice-strict; R:E,S+ETH,Qf,Qb\]

## Machine-Checked Proofs

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 [@Lean2015; @demoura2021lean4; @mathlib2020; @forster2019verified; @kunze2019formal] (11932 lines, 553 theorem/lemma statements). The formalization verifies that the TAUTOLOGY reduction correctly maps tautologies to sufficient coordinate sets. Complexity class membership (coNP-completeness, $\Sigma_2^P$-completeness) follows by composition with standard complexity-theoretic results.

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

::: proposition
[]{#prop:empty-sufficient-constant label="prop:empty-sufficient-constant"} For any decision problem, $$\text{sufficient}(\emptyset)
\iff
\forall s,s'\in S,\ \operatorname{Opt}(s)=\operatorname{Opt}(s').$$ Hence, the $I=\emptyset$ query is exactly a universal constancy check of the decision boundary.
:::

::: proposition
[]{#prop:insufficiency-counterexample label="prop:insufficiency-counterexample"} For any coordinate set $I$, $$\neg\text{sufficient}(I)
\iff
\exists s,s'\in S:\ s_I=s'_I\ \wedge\ \operatorname{Opt}(s)\neq\operatorname{Opt}(s').$$ In particular, $$\neg\text{sufficient}(\emptyset)
\iff
\exists s,s'\in S:\ \operatorname{Opt}(s)\neq\operatorname{Opt}(s').$$
:::

\[D:Ddef:sufficient;Pprop:empty-sufficient-constant, prop:insufficiency-counterexample; R:DM\]

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

This succinct circuit encoding is the standard representation for decision problems in complexity theory; hardness is stated with respect to the input length of the circuit description [@arora2009computational; @papadimitriou1994complexity]. An instance is encoded as:

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

::: remark
[]{#rem:uniform-assumption-discipline label="rem:uniform-assumption-discipline"} All theorem-level claims in this paper are conditional on their stated premises and regime tags; no assumption family is given special status. For each claim, the active assumptions are exactly those appearing in its statement, its regime tag, and its cited mechanized handles.
:::

::: remark
[]{#rem:modal-should label="rem:modal-should"} In this paper, normative modal statements denote contract-conditional necessity: once an agent declares an objective/regime/assumption contract, admissible policy is fixed by typed admissibility and integrity under that contract. No unconditional external moral prescription is asserted.
:::

## Discrete-Time Event Semantics {#sec:discrete-time-semantics}

::: definition
[]{#def:timed-interface-state label="def:timed-interface-state"} For any interface state space $S$, a timed interface state is a pair $$x=(s,t)\in S\times \mathbb{N}.$$ The time coordinate is the natural-number component $t$.
:::

::: definition
[]{#def:decision-tick-event label="def:decision-tick-event"} Fix an interface decision process $(\mathrm{decide},\mathrm{transition})$ with $$\mathrm{decide}:S\to A,\qquad \mathrm{transition}:S\times A\to S.$$ Define one tick by $$\mathrm{tick}(s,t)=\bigl(\mathrm{transition}(s,\mathrm{decide}(s)),\,t+1\bigr).$$ Define $\mathrm{DecisionEvent}(x,y)$ to mean that $y$ is the one-tick successor of $x$ under this rule.
:::

::: proposition
[]{#prop:time-discrete label="prop:time-discrete"} In Definition [\[def:timed-interface-state\]](#def:timed-interface-state){reference-type="ref" reference="def:timed-interface-state"}, time is discrete: $$\forall x\in S\times\mathbb{N},\ \exists k\in\mathbb{N}\ \text{such that}\ x_t=k.$$ Pointwise time equality is decidable for every $k\in\mathbb{N}$: $$x_t=k\ \vee\ x_t\neq k.$$
:::

::: proposition
[]{#prop:decision-unit-time label="prop:decision-unit-time"} Under Definition [\[def:decision-tick-event\]](#def:decision-tick-event){reference-type="ref" reference="def:decision-tick-event"}, for all timed states $x,y$: $$\mathrm{DecisionEvent}(x,y)\ \Longleftrightarrow\ y=\mathrm{tick}(x),$$ and therefore $$\mathrm{DecisionEvent}(x,y)\ \Longrightarrow\ y_t=x_t+1.$$
:::

::: proposition
[]{#prop:run-time-accounting label="prop:run-time-accounting"} Let $\mathrm{run}(n,x)$ be $n$ repeated ticks from $x$, and let $\mathrm{trace}(n,x)$ be the emitted decision sequence. Then: $$\mathrm{run}(n,x)_t = x_t + n,\qquad
\mathrm{run}(n,x)_t - x_t = n,\qquad
|\mathrm{trace}(n,x)|=n.$$ Hence decision count equals elapsed time: $$|\mathrm{trace}(n,x)|=\mathrm{run}(n,x)_t-x_t.$$
:::

::: proposition
[]{#prop:substrate-unit-time label="prop:substrate-unit-time"} For any substrate model that is consistent with the declared interface transition rule, each one-step substrate evolution realizes one interface decision event and advances interface time by one unit. The time update law is invariant under substrate kind.
:::

::: theorem
[]{#thm:regime-coverage label="thm:regime-coverage"} Let $$\mathcal{R}_{\mathrm{static}} =
\{\text{[E]},\ \text{[S+ETH]},\ \text{[Q\_fin:Opt]},\ \text{[Q\_bool:value-entry]},\ \text{[Q\_bool:state-batch]}\}.$$ For each declared regime in $\mathcal{R}_{\mathrm{static}}$, the paper has a theorem-level mechanized core claim. Equivalently, regime typing is complete over the declared static family.
:::

#### Scope Lattice (typed classes and transfer boundary).

::: center
  ---------------------------------------------------------------------------------------------------------------------------------------------------------
  **Layer**                                                                               **Transfer Status**           **Lean handles (representative)**
  --------------------------------------------------------------------------------------- ----------------------------- -----------------------------------
  Static sufficiency class (C1--C4; declared regimes)                                     Internal landscape complete   

                                                                                                                        

  Bridge-admissible adjacent class (one-step deterministic)                               Transfer licensed             

                                                                                                                        

  Non-admissible represented adjacent classes (horizon, stochastic, transition-coupled)   Transfer blocked by witness   

                                                                                                                        
  ---------------------------------------------------------------------------------------------------------------------------------------------------------
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

Operationally: a trained model evaluated with fixed parameters during inference is an agent snapshot for this typing; once parameters or transition-relevant internals are updated online, the object is process-typed and transfer from static sufficiency theorems is blocked unless the one-step bridge conditions are re-established. \[D:Pprop:snapshot-process-typing; R:RA\]

# Interpretive Foundations: Hardness and Solver Claims {#sec:interpretive-foundations}

The claims in later applied sections are theorem-indexed consequences of this section and Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}--[\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"}.

## Structural Complexity vs Representational Hardness

::: definition
[]{#def:structural-complexity label="def:structural-complexity"} For a fixed decision question (e.g., "is $I$ sufficient for $\mathcal{D}$?"; see Remark [\[rem:question-vs-problem\]](#rem:question-vs-problem){reference-type="ref" reference="rem:question-vs-problem"}), *structural complexity* means its placement in standard complexity classes within the formal model (coNP, $\Sigma_2^P$, etc.), as established by class-membership arguments and reductions.
:::

::: definition
[]{#def:representational-hardness label="def:representational-hardness"} For a fixed decision question and an encoding regime $E$ (Section [1.4](#sec:encoding){reference-type="ref" reference="sec:encoding"}), *representational hardness* is the worst-case computational cost incurred by solvers whose input access is restricted to $E$.
:::

In the mechanized architecture model, this is made explicit as a required-work observable and intrinsic lower bound: 'requiredWork' is total realized work, 'hardnessLowerBound' is the intrinsic floor, and 'hardness_is_irreducible_required_work' proves the lower-bound relation for all nonzero use-site counts; 'requiredWork_eq_affine_in_sites' and 'workGrowthDegree' make the site-count growth law explicit.

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

To keep practical corollaries type-safe, we separate *integrity* (what a solver is allowed to assert) from *competence* (what it can cover under a declared regime), following the certifying-algorithms schema [@mcconnell2010certifying; @necula1997proof]. The induced-relation view used below is standard in complexity/computability presentations: algorithms are analyzed as machines deciding languages or computing functions/relations over encodings [@papadimitriou1994complexity; @arora2009computational; @forster2019verified].

::: definition
[]{#def:certifying-solver label="def:certifying-solver"} Fix a decision question $\mathcal{R} \subseteq \mathcal{X}\times\mathcal{Y}$ and an encoding regime $E$ over $\mathcal{X}$. A *certifying solver* is a pair $(Q,V)$ where:

-   $Q$ maps each input $x\in\mathcal{X}$ to either $\mathsf{ABSTAIN}$ or a candidate pair $(y,w)$,

-   $V$ is a polynomial-time checker (in $|{\rm enc}_E(x)|$) with output in $\{0,1\}$.
:::

::: definition
[]{#def:induced-solver-relation label="def:induced-solver-relation"} For any deterministic program $M$ computing a partial map $f_M:\mathcal{X}\rightharpoonup\mathcal{Y}$ on encoded inputs, define $$\mathcal{R}_M
:=
\{(x,y)\in\mathcal{X}\times\mathcal{Y} : f_M(x)\downarrow \ \wedge\ y=f_M(x)\}.$$
:::

::: proposition
[]{#prop:universal-solver-framing label="prop:universal-solver-framing"} Every deterministic computer program that computes a (possibly partial) map on encoded inputs can be framed as a solver for its induced relation (Definition [\[def:induced-solver-relation\]](#def:induced-solver-relation){reference-type="ref" reference="def:induced-solver-relation"}). In this formal sense, all computers are solvers of specific problems.
:::

::: proof
*Proof.* Immediate from Definition [\[def:induced-solver-relation\]](#def:induced-solver-relation){reference-type="ref" reference="def:induced-solver-relation"}: each program induces a relation given by its graph on the domain where it halts. ◻
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

::: corollary
[]{#cor:integrity-universal label="cor:integrity-universal"} Let $M$ be any deterministic program, viewed as a certifying solver pair $(Q,V)$ for some externally fixed target relation $\mathcal{R}$. Then Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"} applies unchanged. Thus epistemic integrity is architecture-universal over computing systems once they are cast as solvers for declared tasks.
:::

::: proof
*Proof.* Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"} quantifies over a relation $\mathcal{R}$ and a certifying pair $(Q,V)$; it does not assume any special implementation substrate. ◻
:::

\[D:Pprop:universal-solver-framing;Ccor:integrity-universal; R:TR\]

::: remark
[]{#rem:external-task-nonvacuity label="rem:external-task-nonvacuity"} If the target relation is chosen post hoc from the program's own behavior (for example, $\mathcal{R}=\mathcal{R}_M$ from Definition [\[def:induced-solver-relation\]](#def:induced-solver-relation){reference-type="ref" reference="def:induced-solver-relation"}), integrity can become tautological and competence claims can be vacuous. Non-vacuous competence claims therefore require the target relation, encoding regime, and resource bound to be declared independently of observed outputs. \[D:Ddef:solver-integrity, def:competence-regime;Pprop:integrity-competence-separation, prop:integrity-resource-bound; R:AR\]
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

::: definition
[]{#def:typed-claim-report label="def:typed-claim-report"} For a declared objective family and regime, a solver-side report is one of:

-   $\mathsf{ABSTAIN}$,

-   $\mathsf{EXACT}$ (claiming exact competence/certification),

-   $\mathsf{EPSILON}(\varepsilon)$ (claiming $\varepsilon$-competence/certification).
:::

::: proposition
[]{#prop:typed-claim-admissibility label="prop:typed-claim-admissibility"} Under Definitions [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}, [\[def:epsilon-competence-regime\]](#def:epsilon-competence-regime){reference-type="ref" reference="def:epsilon-competence-regime"}, and [\[def:typed-claim-report\]](#def:typed-claim-report){reference-type="ref" reference="def:typed-claim-report"}:

-   $\mathsf{ABSTAIN}$ is always admissible;

-   $\mathsf{EXACT}$ is admissible iff exact competence holds;

-   $\mathsf{EPSILON}(\varepsilon)$ is admissible iff $\varepsilon$-competence holds.

Hence claim type and certificate type must match (no cross-typing of uncertified assertions as certified guarantees).
:::

::: definition
[]{#def:evidence-object label="def:evidence-object"} For declared $(\mathcal{R},(\mathcal{R}_\varepsilon)_{\varepsilon\ge 0},\Gamma,Q)$ and report type $r\in\{\mathsf{ABSTAIN},\mathsf{EXACT},\mathsf{EPSILON}(\varepsilon)\}$, *evidence* is a first-class witness object:

-   for $\mathsf{ABSTAIN}$: trivial witness;

-   for $\mathsf{EXACT}$: exact-competence witness;

-   for $\mathsf{EPSILON}(\varepsilon)$: $\varepsilon$-competence witness.
:::

::: proposition
[]{#prop:evidence-admissibility-equivalence label="prop:evidence-admissibility-equivalence"} For any declared contract and report type $r$: $$\text{Evidence object for }r\ \text{exists}
\iff
\text{Claim }r\ \text{is admissible}.$$
:::

\[D:Ddef:evidence-object;Pprop:typed-claim-admissibility, prop:evidence-admissibility-equivalence; R:AR\]

#### Security-game reading (derived).

The typed-report layer can be read as a standard claim-verification game under a declared contract: a reporting algorithm emits a report token $r$ and optional evidence, and a checker accepts if and only if the evidence is valid for $r$. Within this game view, existing results already provide the core security properties: *completeness* for admissible report classes (Proposition [\[prop:evidence-admissibility-equivalence\]](#prop:evidence-admissibility-equivalence){reference-type="ref" reference="prop:evidence-admissibility-equivalence"}), *soundness* against overclaiming (Propositions [\[prop:typed-claim-admissibility\]](#prop:typed-claim-admissibility){reference-type="ref" reference="prop:typed-claim-admissibility"}, [\[prop:exact-requires-evidence\]](#prop:exact-requires-evidence){reference-type="ref" reference="prop:exact-requires-evidence"}), and *evidence-gated confidence* (Propositions [\[prop:certified-confidence-gate\]](#prop:certified-confidence-gate){reference-type="ref" reference="prop:certified-confidence-gate"}, [\[prop:no-evidence-zero-certified\]](#prop:no-evidence-zero-certified){reference-type="ref" reference="prop:no-evidence-zero-certified"}). So integrity is enforced as verifiable claim discipline, not as unchecked payload declaration. \[D:Pprop:typed-claim-admissibility, prop:evidence-admissibility-equivalence, prop:exact-requires-evidence, prop:certified-confidence-gate, prop:no-evidence-zero-certified; R:AR\]

::: definition
[]{#def:signaled-typed-report label="def:signaled-typed-report"} A *signaled typed report* augments the typed report token $r\in\{\mathsf{ABSTAIN},\mathsf{EXACT},\mathsf{EPSILON}(\varepsilon)\}$ with:

-   an optional guess payload $g$,

-   self-reflected confidence $p_{\mathrm{self}}\in[0,1]$,

-   certified confidence $p_{\mathrm{cert}}\in[0,1]$.

-   scalar execution witness $t_{\mathrm{run}}\in\mathbb{N}$ (steps actually run),

-   optional declared bound $B\in\mathbb{N}$.

Here $p_{\mathrm{self}}$ is a self-signal, while $p_{\mathrm{cert}}$ is an evidence-gated signal under the declared contract.
:::

::: definition
[]{#def:signal-consistency label="def:signal-consistency"} For a signaled typed report $(r,g,p_{\mathrm{self}},p_{\mathrm{cert}},t_{\mathrm{run}},B)$, require: $$p_{\mathrm{cert}} > 0 \Rightarrow \exists\ \text{evidence object for }r.$$
:::

::: proposition
[]{#prop:exact-requires-evidence label="prop:exact-requires-evidence"} In the typed claim discipline, $$\text{ClaimAdmissible}(\mathsf{EXACT})
\iff
\exists\ \text{exact evidence object}.$$ Equivalently, admissible exact claims are exactly those with an evidence witness.
:::

::: definition
[]{#def:completion-fraction label="def:completion-fraction"} Completion-fraction semantics are defined only when a positive declared bound exists and covers observed runtime: $$\mathrm{CompletionFractionDefined}
\iff
\exists b>0:\ B=b\ \wedge\ t_{\mathrm{run}}\le b.$$
:::

::: proposition
[]{#prop:certified-confidence-gate label="prop:certified-confidence-gate"} Under Definition [\[def:signal-consistency\]](#def:signal-consistency){reference-type="ref" reference="def:signal-consistency"}, positive certified confidence implies typed admissibility: $$p_{\mathrm{cert}} > 0 \Rightarrow \text{ClaimAdmissible}(r).$$ Thus certified confidence is not a free scalar; it is evidence-gated by the same typed discipline as the report itself.
:::

::: proposition
[]{#prop:no-evidence-zero-certified label="prop:no-evidence-zero-certified"} Under Definition [\[def:signal-consistency\]](#def:signal-consistency){reference-type="ref" reference="def:signal-consistency"}, absence of evidence for the reported type forces: $$\neg\exists\ \text{evidence object for }r
\Rightarrow
p_{\mathrm{cert}}=0.$$
:::

::: corollary
[]{#cor:exact-no-competence-zero-certified label="cor:exact-no-competence-zero-certified"} For exact reports, if exact competence is unavailable on the declared regime/objective, then any signal-consistent report must satisfy: $$p_{\mathrm{cert}} = 0.$$
:::

::: proposition
[]{#prop:steps-run-scalar label="prop:steps-run-scalar"} For every signaled report, the execution witness is an exact natural number and any equality claim about it is decidable: $$\exists k\in\mathbb{N}:\ t_{\mathrm{run}}=k,
\qquad
\forall k\in\mathbb{N},\ (t_{\mathrm{run}}=k)\ \vee\ (t_{\mathrm{run}}\neq k).$$
:::

::: proposition
[]{#prop:no-fraction-without-bound label="prop:no-fraction-without-bound"} If no declared bound is provided ($B=\varnothing$), completion-fraction semantics are undefined: $$B=\varnothing \Rightarrow \neg\,\mathrm{CompletionFractionDefined}.$$
:::

::: proposition
[]{#prop:fraction-defined-under-bound label="prop:fraction-defined-under-bound"} If a positive declared bound is provided and observed runtime is within bound, completion-fraction semantics are defined: $$B=b,\ b>0,\ t_{\mathrm{run}}\le b
\Rightarrow
\mathrm{CompletionFractionDefined}.$$
:::

::: proposition
[]{#prop:abstain-guess-self-signal label="prop:abstain-guess-self-signal"} For any optional guess payload $g$ and any self-reflected confidence $p_{\mathrm{self}}\in[0,1]$, there exists a signal-consistent abstain report $$(\mathsf{ABSTAIN}, g, p_{\mathrm{self}}, 0, 0, \varnothing).$$ Hence the framework is non-binary at the report-signal layer: abstention can carry a tentative answer and self-reflection without upgrading to certified exactness.
:::

::: proposition
[]{#prop:self-confidence-not-certification label="prop:self-confidence-not-certification"} Self-reflected confidence alone does not certify exactness: if exact competence is unavailable, there exist exact-labeled reports with arbitrary $p_{\mathrm{self}}$ that remain inadmissible under zero certified confidence.
:::

\[D:Ddef:signaled-typed-report, def:signal-consistency, def:completion-fraction;Pprop:exact-requires-evidence, prop:certified-confidence-gate, prop:no-evidence-zero-certified, prop:steps-run-scalar, prop:no-fraction-without-bound, prop:fraction-defined-under-bound, prop:abstain-guess-self-signal, prop:self-confidence-not-certification;Ccor:exact-no-competence-zero-certified; R:AR\]

::: definition
[]{#def:declared-budget-slice label="def:declared-budget-slice"} For a declared regime $\Gamma$ over state objects and horizon/budget cut $H\in\mathbb{N}$, define the in-scope slice $$\mathcal{S}_{\Gamma,H}
:=
\{s:\ s\in\Gamma.\mathrm{inScope}\ \wedge\ \mathrm{encLen}_\Gamma(s)\le H\}.$$
:::

::: proposition
[]{#prop:bounded-slice-meta-irrelevance label="prop:bounded-slice-meta-irrelevance"} Fix coordinate $i_\infty$ and declared slice $\mathcal{S}_{\Gamma,H}$ from Definition [\[def:declared-budget-slice\]](#def:declared-budget-slice){reference-type="ref" reference="def:declared-budget-slice"}. If optimizer sets are invariant to $i_\infty$ on that slice, i.e., $$\forall s,s'\in\mathcal{S}_{\Gamma,H},\ 
\Big(\forall j\neq i_\infty,\ s_j=s'_j\Big)
\Rightarrow
\operatorname{Opt}(s)=\operatorname{Opt}(s'),$$ then $i_\infty$ is irrelevant on $\mathcal{S}_{\Gamma,H}$, and hence not relevant for the declared task slice.
:::

\[D:Ddef:declared-budget-slice;Pprop:bounded-slice-meta-irrelevance; R:AR\]

::: definition
[]{#def:goal-class label="def:goal-class"} A *goal class* is a non-empty set of admissible evaluators over a fixed action/state structure: $$\mathcal{G}=(\mathcal{U}_{\mathcal{G}},A,S),\qquad
\varnothing\neq\mathcal{U}_{\mathcal{G}}\subseteq\{U:A\times S\to\mathbb{Q}\}.$$ The solver need not know which $U\in\mathcal{U}_{\mathcal{G}}$ is active; it only knows class-membership constraints.
:::

::: definition
[]{#def:interior-pareto-dominance label="def:interior-pareto-dominance"} For a goal class $\mathcal{G}$ and score model $\sigma:S\times\{1,\ldots,n\}\to\mathbb{Q}$, let $J_{\mathcal{G}}$ be the class-tautological coordinate set. State $s$ *interior-Pareto-dominates* $s'$ on $J_{\mathcal{G}}$ when: $$\forall j\in J_{\mathcal{G}},\ \sigma(s',j)\le \sigma(s,j)
\quad\text{and}\quad
\exists j\in J_{\mathcal{G}},\ \sigma(s',j)<\sigma(s,j).$$
:::

::: proposition
[]{#prop:interior-universal-non-rejection label="prop:interior-universal-non-rejection"} If a state $s$ interior-Pareto-dominates $s'$ on a checked coordinate set $J$, and every admissible evaluator in the goal class is monotone on $J$, then no admissible evaluator strictly prefers $s'$ over $s$ on that checked slice: $$\forall U\in\mathcal{U}_{\mathcal{G}},\ \forall a\in A,\ U(a,s')\le U(a,s).$$
:::

::: proposition
[]{#prop:interior-verification-tractable label="prop:interior-verification-tractable"} If membership in the checked coordinate set is decidable and interior dominance is decidable, then interior verification yields a polynomial-time checker with exact acceptance criterion: $$\exists\ \mathrm{verify}:S\times S\to\{0,1\},\quad
\mathrm{verify}(s,s')=1\iff \text{interior-dominance}(s,s').$$
:::

::: proposition
[]{#prop:interior-one-sidedness label="prop:interior-one-sidedness"} Interior dominance is one-sided and does not imply full coordinate sufficiency: a counterexample pair outside the checked slice can still violate global optimizer equivalence.
:::

::: corollary
[]{#cor:interior-singleton-certificate label="cor:interior-singleton-certificate"} For a singleton checked coordinate $i$, strict improvement on $i$ with class-monotonicity on $\{i\}$ is already a valid interior certificate of non-rejection.
:::

\[D:Ddef:goal-class, def:interior-pareto-dominance;Pprop:interior-universal-non-rejection, prop:interior-verification-tractable, prop:interior-one-sidedness;Ccor:interior-singleton-certificate; R:AR\]

::: definition
[]{#def:rlff-objective label="def:rlff-objective"} Given report type $r\in\{\mathsf{ABSTAIN},\mathsf{EXACT},\mathsf{EPSILON}(\varepsilon)\}$ and declared contract, RLFF assigns base reward by report type when evidence exists and applies an explicit inadmissibility penalty otherwise: $$\mathrm{Reward}(r)=
\begin{cases}
\mathrm{Base}(r), & \text{if evidence for }r\text{ exists},\\
-\mathrm{Penalty}, & \text{otherwise}.
\end{cases}$$
:::

::: proposition
[]{#prop:rlff-maximizer-admissible label="prop:rlff-maximizer-admissible"} If $\mathsf{ABSTAIN}$ reward strictly exceeds the inadmissibility branch, then any global RLFF maximizer must be evidence-backed and therefore admissible under the typed-claim discipline.
:::

::: corollary
[]{#cor:rlff-abstain-no-certs label="cor:rlff-abstain-no-certs"} If $\mathsf{EXACT}$ and $\mathsf{EPSILON}(\varepsilon)$ have no evidence objects while $\mathsf{ABSTAIN}$ beats the inadmissibility branch, then RLFF strictly prefers $\mathsf{ABSTAIN}$ to both report types.
:::

\[D:Ddef:rlff-objective;Pprop:rlff-maximizer-admissible;Ccor:rlff-abstain-no-certs; R:AR\]

::: definition
[]{#def:certainty-inflation label="def:certainty-inflation"} For a typed report $r$, certainty inflation is the state of emitting $r$ without a matching evidence object.
:::

::: proposition
[]{#prop:certainty-inflation-iff-inadmissible label="prop:certainty-inflation-iff-inadmissible"} For every typed report $r$: $$\text{CertaintyInflation}(r)
\iff
\neg\ \text{ClaimAdmissible}(r).$$ For $r=\mathsf{EXACT}$ this is equivalently failure of exact competence.
:::

::: corollary
[]{#cor:hardness-exact-certainty-inflation label="cor:hardness-exact-certainty-inflation"} Under the declared hardness/non-collapse premises that block universal exact admissibility, every exact report is certainty-inflated.
:::

\[D:Ddef:certainty-inflation;Pprop:certainty-inflation-iff-inadmissible;Ccor:hardness-exact-certainty-inflation; R:CR\]

::: definition
[]{#def:raw-certified-bits label="def:raw-certified-bits"} Fix a declared contract and report type $r$. A report-bit model declares:

-   raw report bits $B_{\mathrm{raw}}(r)$ (payload bits in the asserted report token),

-   certificate bits $B_{\mathrm{cert}}(r)$ (bits allocated to the matching evidence class).

Evidence-gated overhead and certified total are then: $$B_{\mathrm{over}}(r)=
\begin{cases}
B_{\mathrm{cert}}(r), & \text{if evidence for }r\text{ exists},\\
0, & \text{otherwise},
\end{cases}
\qquad
B_{\mathrm{total}}(r)=B_{\mathrm{raw}}(r)+B_{\mathrm{over}}(r).$$
:::

::: proposition
[]{#prop:raw-certified-bit-split label="prop:raw-certified-bit-split"} For every typed report $r$: $$B_{\mathrm{total}}(r)=B_{\mathrm{raw}}(r)+B_{\mathrm{over}}(r),$$ with $$\neg\exists\ \text{evidence for }r \Rightarrow B_{\mathrm{over}}(r)=0,\qquad
\exists\ \text{evidence for }r \Rightarrow B_{\mathrm{over}}(r)=B_{\mathrm{cert}}(r).$$ Hence $B_{\mathrm{raw}}(r)\le B_{\mathrm{total}}(r)$ always, and strict inequality holds when evidence exists with positive certificate-bit allocation.
:::

::: theorem
[]{#thm:exact-certified-gap-iff-admissible label="thm:exact-certified-gap-iff-admissible"} Under a report-bit model with positive exact certificate-bit allocation: $$\text{ClaimAdmissible}(\mathsf{EXACT})
\iff
B_{\mathrm{raw}}(\mathsf{EXACT})<B_{\mathrm{total}}(\mathsf{EXACT}).$$ Equivalently: $$B_{\mathrm{total}}(\mathsf{EXACT})=B_{\mathrm{raw}}(\mathsf{EXACT})
\iff
\text{ExactCertaintyInflation}.$$
:::

::: corollary
[]{#cor:hardness-raw-only-exact label="cor:hardness-raw-only-exact"} If exact reporting is inadmissible on the declared contract, then exact accounting collapses to raw-only: $$B_{\mathrm{total}}(\mathsf{EXACT})=B_{\mathrm{raw}}(\mathsf{EXACT}).$$
:::

\[D:Ddef:raw-certified-bits;Tthm:exact-certified-gap-iff-admissible;Pprop:raw-certified-bit-split;Ccor:hardness-raw-only-exact; R:AR\]

::: corollary
[]{#cor:no-uncertified-exact-claim label="cor:no-uncertified-exact-claim"} If exact competence does not hold on the declared regime/objective, then an $\mathsf{EXACT}$ report is inadmissible.
:::

\[D:Pprop:typed-claim-admissibility;Ccor:no-uncertified-exact-claim; R:AR\]

::: proposition
[]{#prop:declared-contract-selection-validity label="prop:declared-contract-selection-validity"} For solver-side reporting, there are two formally distinct layers:

-   **Declared-contract selection layer:** choosing objective family $(\mathcal{R}_\varepsilon)_{\varepsilon\ge 0}$, regime $\Gamma$, and assumption profile;

-   **Validity layer:** once declared, admissibility of $\mathsf{EXACT}/\mathsf{EPSILON}(\varepsilon)/\mathsf{ABSTAIN}$ reports is fixed by certificate-typed rules.

Thus the framework treats contract selection as an external declaration choice, and then enforces mechanically checked admissibility within that declared contract.
:::

::: proof
*Proof.* The validity layer is Proposition [\[prop:typed-claim-admissibility\]](#prop:typed-claim-admissibility){reference-type="ref" reference="prop:typed-claim-admissibility"}: report admissibility is exactly tied to the matching competence certificate type. For exact physical claims outside carve-outs, Proposition [\[prop:outside-excuses-explicit-assumptions\]](#prop:outside-excuses-explicit-assumptions){reference-type="ref" reference="prop:outside-excuses-explicit-assumptions"} and Theorem [\[thm:claim-integrity-meta\]](#thm:claim-integrity-meta){reference-type="ref" reference="thm:claim-integrity-meta"} require explicit assumptions, and Corollary [\[cor:outside-excuses-no-exact-report\]](#cor:outside-excuses-no-exact-report){reference-type="ref" reference="cor:outside-excuses-no-exact-report"} blocks uncertified exact reports under declared non-collapse assumptions. Therefore, once the contract is declared, admissibility is mechanically determined by the typed rules and attached assumption profile. ◻
:::

\[D:Tthm:claim-integrity-meta;Pprop:typed-claim-admissibility, prop:outside-excuses-explicit-assumptions;Ccor:outside-excuses-no-exact-report; R:DC\]

::: definition
[]{#def:exact-claim-excuses label="def:exact-claim-excuses"} For exact physical claims in this framework, we declare four explicit carve-outs:

1.  trivial scope (empty in-scope family),

2.  tractable class (exact competence available in the active regime),

3.  stronger oracle/regime shift (the claim is made under strictly stronger access assumptions),

4.  unbounded resources (budget bounds intentionally removed).
:::

::: definition
[]{#def:explicit-hardness-profile label="def:explicit-hardness-profile"} An explicit hardness-assumption profile for declared class/regime $(\mathcal{R},\Gamma)$ consists of:

-   a non-collapse hypothesis,

-   a collapse implication from universal exact competence on $(\mathcal{R},\Gamma)$.
:::

::: definition
[]{#def:exact-claim-welltyped label="def:exact-claim-welltyped"} An exact physical claim is *well-typed* only if either:

-   at least one carve-out from Definition [\[def:exact-claim-excuses\]](#def:exact-claim-excuses){reference-type="ref" reference="def:exact-claim-excuses"} is explicitly declared, or

-   an explicit hardness-assumption profile (Definition [\[def:explicit-hardness-profile\]](#def:explicit-hardness-profile){reference-type="ref" reference="def:explicit-hardness-profile"}) is explicitly declared.
:::

::: proposition
[]{#prop:outside-excuses-explicit-assumptions label="prop:outside-excuses-explicit-assumptions"} If an exact physical claim is well-typed (Definition [\[def:exact-claim-welltyped\]](#def:exact-claim-welltyped){reference-type="ref" reference="def:exact-claim-welltyped"}) and no carve-out from Definition [\[def:exact-claim-excuses\]](#def:exact-claim-excuses){reference-type="ref" reference="def:exact-claim-excuses"} applies, then an explicit hardness-assumption profile must be present.
:::

::: theorem
[]{#thm:claim-integrity-meta label="thm:claim-integrity-meta"} For declared class/regime objects, every admissible exact-claim policy outside the carve-outs requires explicit assumptions: $$\neg\ \text{Excused (Definition~\ref{def:exact-claim-excuses})}
\ \wedge\
\text{Well-Typed Exact Claim (Definition~\ref{def:exact-claim-welltyped})}
\ \Rightarrow\
\text{Has Explicit Hardness Profile (Definition~\ref{def:explicit-hardness-profile})}.$$
:::

::: proof
*Proof.* Immediate from Proposition [\[prop:outside-excuses-explicit-assumptions\]](#prop:outside-excuses-explicit-assumptions){reference-type="ref" reference="prop:outside-excuses-explicit-assumptions"}; this is the universally quantified theorem-level restatement over the typed claim/regime objects. ◻
:::

::: corollary
[]{#cor:outside-excuses-no-exact-report label="cor:outside-excuses-no-exact-report"} If no carve-out applies and the declared hardness-assumption profile holds, then $\mathsf{EXACT}$ reports are inadmissible for every solver on the declared class/regime.
:::

\[D:Tthm:claim-integrity-meta;Pprop:outside-excuses-explicit-assumptions;Ccor:outside-excuses-no-exact-report; R:CR\]

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

This separation plus Proposition [\[prop:attempted-competence-matrix\]](#prop:attempted-competence-matrix){reference-type="ref" reference="prop:attempted-competence-matrix"} is load-bearing for the regime-conditional trilemma used later: if exact competence is blocked by hardness in a declared regime after an attempted exact procedure, integrity forces one of three responses: abstain, weaken guarantees, or change regime assumptions. \[D:Pprop:attempted-competence-matrix; R:AR\]

#### Mechanized status.

This separation is machine-checked in `DecisionQuotient/IntegrityCompetence.lean` via: and ; the attempted-competence matrix is mechanized via , , and .

::: proposition
[]{#prop:integrity-resource-bound label="prop:integrity-resource-bound"} Let $\Gamma$ be a declared regime whose in-scope family includes all instances of SUFFICIENCY-CHECK and whose declared resource bound is polynomial in the encoding length. If $P\neq coNP$, then no certifying solver is simultaneously integrity-preserving and competent on $\Gamma$ for exact sufficiency. Equivalently, for every integrity-preserving solver, at least one of the competence conjuncts must fail on $\Gamma$: either full non-abstaining coverage fails or the declared budget bound fails.
:::

::: proof
*Proof.* By Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}, competence on $\Gamma$ requires integrity, full in-scope coverage, and budget compliance. Under the coNP-hardness transfer for SUFFICIENCY-CHECK (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), universal competence on this scope would induce a polynomial-time collapse to $P=coNP$. Therefore, under $P\neq coNP$, the full competence predicate cannot hold. Since integrity alone is satisfiable (Proposition [\[prop:integrity-competence-separation\]](#prop:integrity-competence-separation){reference-type="ref" reference="prop:integrity-competence-separation"}, via always-abstain), the obstruction is exactly competence coverage/budget under the declared regime. \[D:Tthm:sufficiency-conp;Pprop:integrity-competence-separation, prop:integrity-resource-bound; R:AR\] ◻
:::

::: proposition
[]{#prop:physics-no-universal-exact label="prop:physics-no-universal-exact"} Fix any declared physical/task class representable by relation $\mathcal{R}$ and regime $\Gamma$ in the certifying-solver model. If $$\big(\exists Q,\ \mathrm{CompetentOn}(\mathcal{R},\Gamma,Q)\big)\ \Rightarrow\ (P=coNP),$$ then under $P\neq coNP$ there is no universally exact-competent solver for that declared class.
:::

::: corollary
[]{#cor:physics-no-universal-exact-claim label="cor:physics-no-universal-exact-claim"} Under the same premises as Proposition [\[prop:physics-no-universal-exact\]](#prop:physics-no-universal-exact){reference-type="ref" reference="prop:physics-no-universal-exact"}, and under the typed-claim discipline of Definition [\[def:typed-claim-report\]](#def:typed-claim-report){reference-type="ref" reference="def:typed-claim-report"}, an $\mathsf{EXACT}$ report is inadmissible for every solver on that declared class. Hence admissible reporting must use $\mathsf{ABSTAIN}$ or explicitly weakened guarantees.
:::

\[D:Pprop:physics-no-universal-exact;Ccor:physics-no-universal-exact-claim; R:CR\]


# Computational Complexity of Decision-Relevant Uncertainty {#sec:hardness}

This section establishes the computational complexity of information sufficiency, formalized as coordinate sufficiency, for an arbitrary decision problem $\mathcal{D}$ with factored state space. Because the problems below are parameterized by $\mathcal{D}$, and the $(A, S, U)$ tuple captures any problem with choices under structured information (Remark [\[rem:universality\]](#rem:universality){reference-type="ref" reference="rem:universality"}), the hardness results are universal: they apply to every problem with coordinate structure, not to a specific problem domain. We prove three main results:

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

Classical coNP-completeness methodology follows standard NP/coNP reduction frameworks and polynomial-time many-one reducibility [@papadimitriou1994complexity; @arora2009computational]. We instantiate that framework for SUFFICIENCY-CHECK with a mechanized TAUTOLOGY reduction.

::: theorem
[]{#thm:sufficiency-conp label="thm:sufficiency-conp"} SUFFICIENCY-CHECK is coNP-complete.
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

The second-level hardness template used here follows canonical $\Sigma_2^P$ polynomial-hierarchy characterizations [@papadimitriou1994complexity; @arora2009computational], instantiated to the anchor formulation below.

::: theorem
[]{#thm:anchor-sigma2p label="thm:anchor-sigma2p"} ANCHOR-SUFFICIENCY is $\Sigma_2^P$-complete (already for Boolean coordinate spaces).
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

The results of this paper give $\varepsilon$ formal complexity consequences. By Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}, determining the minimal sufficient coordinate set is coNP-complete under the succinct encoding. By Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}, under ETH there exist succinct instances requiring $2^{\Omega(n)}$ time to verify sufficiency. In the formal Boolean-coordinate collapse model, size-bounded $\varepsilon=0$ search is exactly the relevance-cardinality predicate (*Lean:* `S2P.min_representationGap_zero_iff_relevant_card`). Together: for an agent encoded as a succinct circuit, the worst-case cost of determining whether its own coordinate attention set is minimal is exponential in the number of input coordinates (under ETH). The gap $\varepsilon$ is not merely unnamed; it is *computationally irreducible*: no polynomial-time algorithm solves all succinct instances (assuming $\mathrm{P} \neq coNP$), and the hard instance family requires $2^{\Omega(n)}$ time.

#### Physical agents as circuits.

Any physical agent that selects actions based on sensory state can be modeled, in the static snapshot, as a circuit: sensory inputs are coordinates $X_1, \ldots, X_n$; the agent's internal computation maps states to actions; and the quality of that mapping is measured by a utility function $U$. \[D:prop:snapshot-process-typing, prop:bridge-transfer-scope; R:\[bridge-admissible snapshot\]\] The explicit-state encoding (truth table) of this mapping has size exponential in the number of sensory dimensions. No physical agent can store it. \[D:thm:dichotomy; R:\[E\] vs \[S+ETH\]\] Every physical agent is therefore a succinct encoding, a circuit whose size is bounded by physical resources (neurons, synapses, transistors, parameters) rather than by the size of the state space it navigates. \[D:thm:dichotomy; R:\[S\]\]

This is not a metaphor. A biological nervous system is a feedforward or recurrent circuit that takes sensory state as input and produces motor commands as output. \[D:prop:snapshot-process-typing; R:\[represented adjacent class\]\] A trained neural network is a parameterized circuit. \[D:prop:snapshot-process-typing; R:\[represented adjacent class\]\] In both cases, the agent *is* a succinct encoding of a utility-to-action mapping, and the question "is this agent attending to the right inputs?" is exactly SUFFICIENCY-CHECK under the succinct encoding. \[D:thm:config-reduction, thm:sufficiency-conp; R:\[S\]\] The compression that makes a circuit physically realizable, with polynomial size rather than exponential size, is the same compression that makes self-verification exponentially costly in the worst case: the state space the circuit compressed away is precisely the domain that must be exhaustively checked to certify sufficiency. \[D:thm:dichotomy, prop:query-regime-obstruction; R:\[S+ETH\],\[Q_fin\]\]

#### The simplicity tax as $\varepsilon$.

The simplicity tax (Definition [\[def:simplicity-tax\]](#def:simplicity-tax){reference-type="ref" reference="def:simplicity-tax"}) measures $|\mathrm{Gap}(M,P)| = |R(P) \setminus A(M)|$: the number of decision-relevant coordinates that the agent's model does not handle natively. In the $\varepsilon$ decomposition above, this is exactly the unattended-relevant component $|R_{\mathrm{rel}}\setminus I|$ (*Lean:* `S2P.representationGap_missing_eq_gapCard`, `S2P.representationGap_eq_waste_plus_missing`). For a physical agent modeled as a circuit, this is the coordinate-level manifestation of $\varepsilon$: the agent attends to a superset of what is necessary, or fails to attend to coordinates that are relevant, and faces worst-case cost exponential in $n$ to verify which case holds (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}). Theorem [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"} then says the total relevance budget is conserved: unhandled coordinates are not eliminated, only redistributed as external per-site cost.

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

**Part 2 (Succinct ETH lower bound, worst case):** A strengthened version of the TAUTOLOGY reduction used in Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} produces a family of instances in which the minimal sufficient set has size $k^* = n$: given a Boolean formula $\varphi$ over $n$ variables, we construct a decision problem with $n$ coordinates such that if $\varphi$ is not a tautology then *every* coordinate is decision-relevant (thus $k^*=n$). This strengthening is mechanized in Lean (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"}). Under the Exponential Time Hypothesis (ETH) [@impagliazzo2001complexity; @arora2009computational], TAUTOLOGY requires time $2^{\Omega(n)}$ in the succinct encoding, so SUFFICIENCY-CHECK inherits a $2^{\Omega(n)}$ worst-case lower bound via this reduction. ◻
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
*Proof.* This is exactly the finite-state indistinguishability theorem . For any $|Q|<|S|$, there is an unqueried hidden state $s_0$ producing oracle-indistinguishable yes/no instances with opposite truth values on the $I=\emptyset$ subproblem. Since SUFFICIENCY-CHECK contains that subproblem, fewer than $|S|$ queries cannot be correct on both instances, yielding the $\Omega(|S|)$ worst-case lower bound. ◻
:::

::: corollary
[]{#cor:information-barrier-query label="cor:information-barrier-query"} For the fixed sufficiency question, finite query interfaces induce an information barrier:

-   (Opt-oracle): with $|Q|<|S|$, there exist yes/no instances indistinguishable on all queried states but with opposite truth values on the $I=\emptyset$ subproblem.

-   value-entry and state-batch interfaces preserve the same obstruction at cardinality $<2^n$.

Hence the barrier is representational-access based: without querying enough of the hidden state support, exact certification is blocked by indistinguishability rather than by search-strategy choice.
:::

::: corollary
[]{#cor:query-obstruction-bool label="cor:query-obstruction-bool"} In the Boolean-coordinate state space $S=\{0,1\}^n$, Proposition [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"} yields the familiar $\Omega(2^n)$ worst-case query lower bound for Opt-oracle access.
:::

::: proposition
[]{#prop:query-value-entry-lb label="prop:query-value-entry-lb"} In the mechanized Boolean value-entry query submodel \[Q_bool\], for any deterministic procedure using fewer than $2^n$ value-entry queries $(a,s)\mapsto U(a,s)$, there exist two queried-value-indistinguishable instances with opposite truth values for SUFFICIENCY-CHECK on the $I=\emptyset$ subproblem. Therefore worst-case value-entry query complexity is also $\Omega(2^n)$.
:::

::: proof
*Proof.* The theorem constructs, for any query set of cardinality $<2^n$, an unqueried hidden state $s_0$ and a yes/no instance pair that agree on all queried values but disagree on $\emptyset$-sufficiency. The auxiliary bound ensures that fewer than $2^n$ value-entry queries cannot cover all states, so the indistinguishability argument applies in the worst case. ◻
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

The structural reason for this separation is enumerable access. Under the explicit-state encoding, the mapping $s \mapsto \operatorname{Opt}(s)$ is directly inspectable and sufficiency verification reduces to scanning state pairs, at cost polynomial in $|S|$. Under succinct encoding, the circuit compresses an exponential state space into polynomial size; universal verification over that compressed domain, namely "for all $s, s'$ with $s_I = s'_I$, does $\operatorname{Opt}(s) = \operatorname{Opt}(s')$?", carries worst-case cost exponential in $n$, because the domain the circuit compressed away cannot be reconstructed without undoing the compression.

## Budgeted Physical Crossover

The \[E\] vs \[S\] split can be typed against an explicit physical budget. Let $E(n)$ and $S(n)$ denote explicit and succinct representation sizes for the same decision question at scale parameter $n$, and let $B$ be a hard representation budget.

::: proposition
[]{#prop:budgeted-crossover label="prop:budgeted-crossover"} If $E(n) > B$ and $S(n) \le B$ for some $n$, then explicit representation is infeasible at $(B,n)$ while succinct representation remains feasible at $(B,n)$.
:::

::: proof
*Proof.* This is exactly the definitional split encoded in : explicit infeasibility is $B < E(n)$ and succinct feasibility is $S(n)\le B$. The theorem returns both conjuncts. ◻
:::

::: proposition
[]{#prop:crossover-above-cap label="prop:crossover-above-cap"} Assume there is a global succinct-size cap $C$ and explicit size is unbounded: $$\forall n,\ S(n)\le C,\qquad
\forall B,\ \exists n,\ B < E(n).$$ Then for every budget $B\ge C$, there exists a crossover witness at budget $B$.
:::

::: proof
*Proof.* Fix $B\ge C$. By unboundedness of $E$, choose $n$ with $B < E(n)$. By the cap assumption, $S(n)\le C\le B$, so $(B,n)$ is a crossover witness. The mechanized closure theorem is . ◻
:::

::: proposition
[]{#prop:crossover-not-certification label="prop:crossover-not-certification"} Fix any collapse schema "exact certification competence $\Rightarrow$ complexity collapse" for the target exact-certification predicate. Under the corresponding non-collapse assumption, exact-certification competence is impossible even when a budgeted crossover witness exists.
:::

::: proof
*Proof.* The mechanized theorem bundles the crossover split with the same logical closure used in Proposition [\[prop:integrity-resource-bound\]](#prop:integrity-resource-bound){reference-type="ref" reference="prop:integrity-resource-bound"}: representational feasibility and certification hardness are distinct predicates. ◻
:::

::: proposition
[]{#prop:crossover-policy label="prop:crossover-policy"} In the certifying-solver model (Definitions [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"}--[\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}), assume:

-   a budgeted crossover witness at $(B,n)$,

-   the same collapse implication as Proposition [\[prop:integrity-resource-bound\]](#prop:integrity-resource-bound){reference-type="ref" reference="prop:integrity-resource-bound"},

-   a solver that is integrity-preserving for the declared relation.

Then either full in-scope non-abstaining coverage fails, or declared budget compliance fails. Equivalently, in uncertified hardness-blocked regions, integrity is compatible with $\mathsf{ABSTAIN}/\mathsf{UNKNOWN}$ but not with unconditional exact-competence claims.
:::

## Thermodynamic Lift in Declared Model

The crossover and hardness statements are complexity-theoretic. The thermodynamic lift follows the same assumption discipline as the rest of the paper: claims are exactly those derivable from the declared conversion model and declared bit-operation lower-bound premises.

::: proposition
[]{#prop:thermo-lift label="prop:thermo-lift"} Fix a declared thermodynamic conversion model with constants $(\lambda,\rho)$ where $\lambda$ lower-bounds energy per irreversible bit operation and $\rho$ lower-bounds carbon per joule. If a bit-operation lower bound $b_{\mathrm{LB}} \le b_{\mathrm{used}}$ holds, then: $$E_{\mathrm{LB}}=\lambda b_{\mathrm{LB}} \le \lambda b_{\mathrm{used}},\qquad
C_{\mathrm{LB}}=\rho E_{\mathrm{LB}} \le \rho(\lambda b_{\mathrm{used}}).$$
:::

::: proposition
[]{#prop:thermo-hardness-bundle label="prop:thermo-hardness-bundle"} Under the same non-collapse/collapse schema used by Proposition [\[prop:integrity-resource-bound\]](#prop:integrity-resource-bound){reference-type="ref" reference="prop:integrity-resource-bound"}, exact-certification competence is impossible; combined with a declared bit-operation lower bound, this yields simultaneous lower bounds on energy and carbon in the declared conversion model.
:::

::: proposition
[]{#prop:thermo-mandatory-cost label="prop:thermo-mandatory-cost"} Within the declared linear thermodynamic model, if $$\lambda > 0,\quad \rho > 0,\quad b_{\mathrm{LB}} > 0,$$ then both lower bounds are strictly positive: $$E_{\mathrm{LB}}=\lambda b_{\mathrm{LB}} > 0,\qquad
C_{\mathrm{LB}}=\rho E_{\mathrm{LB}} > 0.$$
:::

::: proposition
[]{#prop:thermo-conservation-additive label="prop:thermo-conservation-additive"} Within the same declared linear model, lower-bound accounting is additive over composed bit-operation lower bounds: $$E_{\mathrm{LB}}(b_1+b_2)=E_{\mathrm{LB}}(b_1)+E_{\mathrm{LB}}(b_2),\qquad
C_{\mathrm{LB}}(b_1+b_2)=C_{\mathrm{LB}}(b_1)+C_{\mathrm{LB}}(b_2).$$
:::


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
Proposition [\[prop:heuristic-reusability\]](#prop:heuristic-reusability){reference-type="ref" reference="prop:heuristic-reusability"} removes the complexity-theoretic obstruction to integrity-preserving action on detectable tractable instances: integrity no longer *forces* abstention. Whether the agent acts still requires competence (Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}): budget and coverage must also be satisfied. An agent that detects structure class $\mathcal{C}$, applies the corresponding polynomial checker, and abstains when detection fails maintains integrity; it never claims sufficiency without verification. Mistaking the heuristic for the general solution, claiming polynomial-time competence on a coNP-hard problem, violates integrity (Proposition [\[prop:integrity-resource-bound\]](#prop:integrity-resource-bound){reference-type="ref" reference="prop:integrity-resource-bound"}).
:::


# Regime-Conditional Corollaries {#sec:engineering-justification}

This section derives regime-typed engineering corollaries from the core complexity theorems. Theorem [\[thm:config-reduction\]](#thm:config-reduction){reference-type="ref" reference="thm:config-reduction"} maps configuration simplification to SUFFICIENCY-CHECK; Theorems [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}, and [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} then yield exact minimization consequences under \[S\] and \[S+ETH\].

Regime tags used below follow Section [\[sec:model-contract\]](#sec:model-contract){reference-type="ref" reference="sec:model-contract"}: \[S\], \[S+ETH\], \[E\], \[S_bool\]. Any prescription that requires exact minimization is constrained by these theorem-level bounds. \[D:Tthm:sufficiency-conp, thm:minsuff-conp, thm:dichotomy; R:S,S+ETH\] Theorem [\[thm:overmodel-diagnostic\]](#thm:overmodel-diagnostic){reference-type="ref" reference="thm:overmodel-diagnostic"} implies that persistent failure to isolate a minimal sufficient set is a boundary-characterization signal in the current model, not a universal irreducibility claim. \[D:Tthm:overmodel-diagnostic; R:S\]

#### Conditional rationality criterion.

For the objective "minimize verified total cost while preserving integrity," persistent over-specification is admissible only in the *attempted competence failure* cell (Definition [\[def:attempted-competence-failure\]](#def:attempted-competence-failure){reference-type="ref" reference="def:attempted-competence-failure"}): after an attempted exact procedure, if exact irrelevance cannot be certified efficiently, integrity retains uncertified coordinates rather than excluding them. \[D:Pprop:attempted-competence-matrix; R:AR\] When exact competence is available in the active regime (e.g., Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} and the exact-identifiability criterion), proven-irrelevant coordinates are removable; persistent over-specification is irrational for that same objective. \[D:Tthm:tractable;Pprop:attempted-competence-matrix; R:E,STR\] Proposition [\[prop:attempted-competence-matrix\]](#prop:attempted-competence-matrix){reference-type="ref" reference="prop:attempted-competence-matrix"} makes this explicit: in the integrity-preserving matrix, one cell is rational and three are irrational, so irrationality is the default verdict. \[D:Pprop:attempted-competence-matrix; R:AR\]

::: remark
All claims in this section are formal corollaries under the declared model assumptions.

-   Competence claims are indexed by the regime tuple of Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"}; prescriptions are meaningful only relative to feasible resources under that regime (bounded-rationality feasibility discipline) [@sep_bounded_rationality; @arora2009computational]. \[D:Pprop:integrity-competence-separation; R:AR\]

-   Integrity (Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"}) forbids overclaiming beyond certifiable outputs; $\mathsf{ABSTAIN}$/$\mathsf{UNKNOWN}$ is first-class when certification is unavailable. \[D:Pprop:integrity-competence-separation; R:AR\]

-   Therefore, hardness results imply a regime-conditional trilemma: abstain, weaken guarantees (heuristics/approximation), or change encoding/structural assumptions to recover competence. \[D:Tthm:sufficiency-conp, thm:dichotomy;Pprop:attempted-competence-matrix; R:S,S+ETH\]
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

Within \[S+ETH\], persistent over-specification is unresolved boundary characterization, not proof that all included parameters are intrinsically necessary. Conversely, when exact competence is available in the active regime, certifiably irrelevant coordinates are removable; persistence is irrational for the same cost-minimization objective. \[D:Tthm:cost-asymmetry-eth;Pprop:attempted-competence-matrix; R:S+ETH\],\[tractable active regime\]
:::

::: proof
*Proof.* Under ETH, the TAUTOLOGY reduction used in Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} yields a $2^{\Omega(n)}$ worst-case lower bound for SUFFICIENCY-CHECK in the succinct encoding. Any exact algorithm that outputs a minimum sufficient set can decide whether the optimum size is $0$ by checking whether the returned set is empty; this is exactly the SUFFICIENCY-CHECK query for $I=\emptyset$. Hence exact minimal-set finding inherits the same exponential worst-case lower bound.

Maintaining $k$ extra parameters incurs:

-   Documentation cost: $O(k)$ entries

-   Testing cost: $O(k)$ test cases

-   Migration cost: $O(k)$ parameters to update

Total maintenance cost is $C_{\text{over}}(k) = O(k)$.

The eventual dominance step is mechanized in : for fixed linear-overhead parameter $k$ and additive constant $C_{\text{under}}$ there is $n_0$ such that $k < 2^n + C_{\text{under}}$ for all $n \ge n_0$. Therefore: $$C_{\text{over}}(k) \ll C_{\text{find}}(n)$$

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

**1. Conservative retention under unresolved relevance.** If irrelevance cannot be certified efficiently under the active regime, the admissible policy is to retain a conservative superset of parameters. \[D:Tthm:overmodel-diagnostic; R:S\]

**2. Heuristic selection as weakened-guarantee mode.** Under \[S+ETH\], exact global minimization can be exponentially costly in the worst case (Theorem [\[thm:cost-asymmetry-eth\]](#thm:cost-asymmetry-eth){reference-type="ref" reference="thm:cost-asymmetry-eth"}); methods such as AIC/BIC/cross-validation instantiate the "weaken guarantees" branch of Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"} [@akaike1974new; @schwarz1978estimating; @stone1974cross; @guyon2003introduction; @pearl2009causality]. \[D:Tthm:cost-asymmetry-eth; R:S+ETH\]

**3. Full-parameter inclusion as an $O(n)$ upper-bound strategy.** Under \[S+ETH\], if exact minimization is unresolved, including all $n$ parameters is an $O(n)$ maintenance upper-bound policy that avoids false irrelevance claims. \[D:Tthm:cost-asymmetry-eth; R:S+ETH\]

**4. Irrationality outside attempted-competence-failure conditions.** If the active regime admits exact competence (tractable structural-access conditions or exact relevance identifiability), or if exact competence was never actually attempted, continued over-specification is irrational; hardness no longer justifies it for the stated objective. \[D:Tthm:tractable;Pprop:attempted-competence-matrix; R:TA\]

These corollaries are direct consequences of the hardness/tractability landscape: over-specification is an attempted-competence-failure policy, not a default optimum. Outside that cell, the admissible exits are to shift to tractable regimes from Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} or adopt explicit approximation commitments. \[D:Tthm:tractable;Pprop:attempted-competence-matrix; R:RG\]

[^1]: Naive subset enumeration still gives an intuitive baseline of $O(2^n)$ checks, but that is an algorithmic upper bound; the theorem below uses ETH for the lower-bound argument.


# Dominance Theorems for Hardness Placement {#sec:implications}

Regime for this section: the mechanized Boolean-coordinate model \[S_bool\] plus the architecture cost model defined below. The centralization-vs-distribution framing follows established software-architecture criteria about modular decomposition and long-run maintenance tradeoffs [@parnas1972criteria; @brooks1987no; @bass2012software; @shaw1996software].

## Over-Specification as Diagnostic Signal

::: corollary
[]{#cor:overmodel-diagnostic-implication label="cor:overmodel-diagnostic-implication"} In the mechanized Boolean-coordinate model, if a coordinate is relevant and omitted from a candidate set $I$, then $I$ is not sufficient.
:::

::: proof
*Proof.* This is the contrapositive of . ◻
:::

::: corollary
[]{#cor:exact-identifiability label="cor:exact-identifiability"} In the mechanized Boolean-coordinate model, for any candidate set $I$: $$I \text{ is exactly relevance-identifying}
\iff
\bigl(I \text{ is sufficient and } I \subseteq R_{\mathrm{rel}}\bigr),$$ where $R_{\mathrm{rel}}$ is the full relevant-coordinate set.
:::

::: proof
*Proof.* This is exactly , with $R_{\mathrm{rel}}=\texttt{relevantFinset}$. ◻
:::

::: remark
[]{#rem:overmodel-conditional label="rem:overmodel-conditional"} In this paper's formal typing, persistent over-specification is admissible only under attempted competence failure: after an attempted exact procedure, exact relevance competence remains unavailable in the active regime, so integrity retains uncertified coordinates (Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"}; Section [\[sec:engineering-justification\]](#sec:engineering-justification){reference-type="ref" reference="sec:engineering-justification"}). \[D:Pprop:attempted-competence-matrix; R:AR\] Once exact competence is available in the active regime (Corollaries [\[cor:practice-bounded\]](#cor:practice-bounded){reference-type="ref" reference="cor:practice-bounded"}--[\[cor:practice-tree\]](#cor:practice-tree){reference-type="ref" reference="cor:practice-tree"} together with Corollary [\[cor:exact-identifiability\]](#cor:exact-identifiability){reference-type="ref" reference="cor:exact-identifiability"}), certifiably irrelevant coordinates are removable; persistent over-specification is irrational for the same objective (verified total-cost minimization). \[D:Tthm:tractable;Pprop:attempted-competence-matrix; R:TA\]
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
*Proof.* By , sufficiency of size $\le k$ is equivalent to a relevance-cardinality bound $\le k$ in the Boolean-coordinate model. ◻
:::

::: corollary
[]{#cor:practice-bounded label="cor:practice-bounded"} When the bounded-action or explicit-state conditions of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} hold, minimal modeling can be solved in polynomial time in the stated input size.
:::

::: proof
*Proof.* This is the bounded-regime branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as . ◻
:::

::: corollary
[]{#cor:practice-structured label="cor:practice-structured"} When utility is separable with explicit factors, sufficiency checking is polynomial in the explicit-state regime.
:::

::: proof
*Proof.* This is the separable-utility branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as . ◻
:::

::: corollary
[]{#cor:practice-tree label="cor:practice-tree"} When utility factors form a tree structure with explicit local factors, sufficiency checking is polynomial in the explicit-state regime.
:::

::: proof
*Proof.* This is the tree-factor branch of Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}, mechanized as . ◻
:::

::: corollary
[]{#cor:practice-unstructured label="cor:practice-unstructured"} There is a machine-checked family of reduction instances where, for non-tautological source formulas, every coordinate is relevant ($k^*=n$), exhibiting worst-case boundary complexity.
:::

::: proof
*Proof.* The strengthened reduction proves that non-tautological source formulas induce instances where every coordinate is relevant; this is mechanized as . ◻
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
*Proof.* (1) and (2) are exactly the bundled theorem . (3) is exactly . ◻
:::

::: corollary
[]{#cor:right-wrong-hardness label="cor:right-wrong-hardness"} In the linear model, a right-hardness architecture strictly dominates a wrong-hardness architecture once use-site count exceeds central one-time hardness. Formally, for architectures $S_{\mathrm{right}}, S_{\mathrm{wrong}}$ over the same problem family, if $S_{\mathrm{right}}$ has right hardness, $S_{\mathrm{wrong}}$ has wrong hardness, and $n > H_{\mathrm{central}}(S_{\mathrm{right}})$, then $$H_{\mathrm{central}}(S_{\mathrm{right}}) + n\,H_{\mathrm{distributed}}(S_{\mathrm{right}})
<
H_{\mathrm{central}}(S_{\mathrm{wrong}}) + n\,H_{\mathrm{distributed}}(S_{\mathrm{wrong}}).$$
:::

::: proof
*Proof.* This is the mechanized theorem . ◻
:::

::: proposition
[]{#prop:dominance-modes label="prop:dominance-modes"} This section uses two linear-model dominance modes plus generalized nonlinear dominance and boundary modes:

1.  **Strict threshold dominance:** Corollary [\[cor:right-wrong-hardness\]](#cor:right-wrong-hardness){reference-type="ref" reference="cor:right-wrong-hardness"} gives strict inequality once $n > H_{\mathrm{central}}(S_{\mathrm{right}})$.

2.  **Global weak dominance:** under the decomposition identity used in , centralized hardness placement is never worse for all $n\ge 1$.

3.  **Generalized nonlinear dominance:** under bounded-vs-growing site-cost assumptions (Theorem [\[thm:generalized-dominance\]](#thm:generalized-dominance){reference-type="ref" reference="thm:generalized-dominance"}), right placement strictly dominates beyond a finite threshold without assuming linear per-site cost.

4.  **Generalized boundary mode:** without those growth-separation assumptions, strict dominance is not guaranteed (Proposition [\[prop:generalized-assumption-boundary\]](#prop:generalized-assumption-boundary){reference-type="ref" reference="prop:generalized-assumption-boundary"}).
:::

::: proof
*Proof.* Part (1) is Corollary [\[cor:right-wrong-hardness\]](#cor:right-wrong-hardness){reference-type="ref" reference="cor:right-wrong-hardness"}. Part (2) is exactly . Part (3) is Theorem [\[thm:generalized-dominance\]](#thm:generalized-dominance){reference-type="ref" reference="thm:generalized-dominance"}. Part (4) is Proposition [\[prop:generalized-assumption-boundary\]](#prop:generalized-assumption-boundary){reference-type="ref" reference="prop:generalized-assumption-boundary"}. ◻
:::

**Illustrative Instantiation (Type Systems).** Consider a capability $C$ (e.g., provenance tracking) with one-time central cost $H_{\text{central}}$ and per-site manual cost $H_{\text{distributed}}$:

::: center
  **Approach**                  $H_{\text{central}}$     $H_{\text{distributed}}$
  ---------------------------- ----------------------- -----------------------------
  Native type system support    High (learning cost)    Low (type checker enforces)
  Manual implementation         Low (no new concepts)   High (reimplement per site)
:::

The table is schematic; the formal statement is Corollary [\[cor:type-system-threshold\]](#cor:type-system-threshold){reference-type="ref" reference="cor:type-system-threshold"}. The type-theoretic intuition behind this instantiation is consistent with classic accounts of abstraction and static interface guarantees [@Cardelli1985; @reynolds1983types; @pierce2002types; @liskov1994behavioral; @siek2006gradual; @gamma1994design].

::: corollary
[]{#cor:type-system-threshold label="cor:type-system-threshold"} For the formal native-vs-manual architecture instance, native support has lower total realized cost for all $$n > H_{\mathrm{baseline}}(P),$$ where $H_{\mathrm{baseline}}(P)$ corresponds to the Lean identifier `intrinsicDOF`(P) in module `HardnessDistribution`.
:::

::: proof
*Proof.* Immediate from . ◻
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
*Proof.* This is exactly the mechanized theorem . ◻
:::

::: corollary
[]{#cor:generalized-eventual-dominance label="cor:generalized-eventual-dominance"} If condition (1) above holds and there exists $N$ such that condition (2) holds for all $m\ge N$, then there exists $N_0$ such that for all $n\ge N_0$, $$H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{right}},n)
<
H_{\text{total}}^{\mathrm{gen}}(S_{\mathrm{wrong}},n).$$
:::

::: proof
*Proof.* Immediate from . ◻
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

The load-bearing fact in this section is not the set identity itself; it is the difficulty of shrinking the required set $R(P)$ in the first place. By Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} (and Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} for minimization), exact relevance identification is intractable in the worst case under succinct encoding. The identities below therefore quantify how unresolved relevance is redistributed between central and per-site work. \[D:Tthm:sufficiency-conp, thm:minsuff-conp; R:S\]

::: definition
Let $R(P)$ be the required dimensions (those affecting $\operatorname{Opt}$) and $A(M)$ the dimensions model $M$ handles natively. The *expressive gap* is $\text{Gap}(M,P) = R(P) \setminus A(M)$.
:::

::: definition
[]{#def:simplicity-tax label="def:simplicity-tax"} The *simplicity tax* is the size of the expressive gap: $$\text{SimplicityTax}(M,P) := |\text{Gap}(M,P)|.$$
:::

::: theorem
[]{#thm:tax-conservation label="thm:tax-conservation"} $|\text{Gap}(M, P)| + |R(P) \cap A(M)| = |R(P)|$. The total cannot be reduced, only redistributed between "handled natively" and "handled externally."
:::

::: proof
*Proof.* In the finite-coordinate model this is the exact set-cardinality identity $$|R\setminus A| + |R\cap A| = |R|,$$ formalized as . ◻
:::

::: remark
The algebraic identity in Theorem [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"} is elementary. Its force comes from upstream hardness: reducing $|R(P)|$ by exact relevance minimization is worst-case intractable under the succinct encoding, so redistribution is often the only tractable lever available.
:::

::: theorem
[]{#thm:tax-grows label="thm:tax-grows"} For $n$ decision sites: $$\text{TotalExternalWork} = n \times \text{SimplicityTax}(M, P).$$
:::

::: proof
*Proof.* This is by definition of per-site externalization and is mechanized as . ◻
:::

::: theorem
[]{#thm:amortization label="thm:amortization"} Let $H_{\text{central}}$ be the one-time cost of using a complete model. There exists $$n^* = \left\lfloor \frac{H_{\text{central}}}{\text{SimplicityTax}(M,P)} \right\rfloor$$ such that for $n > n^*$, the complete model has lower total cost.
:::

::: proof
*Proof.* For positive per-site tax, the threshold inequality $$n > \left\lfloor \frac{H_{\text{central}}}{\text{SimplicityTax}} \right\rfloor
\implies
H_{\text{central}} < n\cdot \text{SimplicityTax}$$ is mechanized as . ◻
:::

::: corollary
[]{#cor:gap-externalization label="cor:gap-externalization"} If $\text{Gap}(M,P)\neq\emptyset$, then external handling cost scales linearly with the number of decision sites.
:::

::: proof
*Proof.* The exact linear form is . When the gap is nonempty (positive tax), monotone growth with $n$ is . ◻
:::

::: corollary
[]{#cor:gap-minimization-hard label="cor:gap-minimization-hard"} For mechanized Boolean-coordinate instances, "there exists a sufficient set of size at most $k$" is equivalent to "the relevant-coordinate set has cardinality at most $k$."
:::

::: proof
*Proof.* This is . ◻
:::

Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} provides theorem statements and module paths for the corresponding Lean formalization.


# Related Work {#sec:related}

## Formalized Complexity and Mechanized Proof Infrastructure

Formalizing complexity-theoretic arguments in proof assistants remains comparatively sparse. Lean and Mathlib provide the current host environment for this artifact [@Lean2015; @demoura2021lean4; @mathlib2020]. Closest mechanized precedents include verified computability/complexity developments in Coq and Isabelle [@forster2019verified; @kunze2019formal; @nipkow2002isabelle; @nipkow2014concrete; @haslbeck2016verified], and certifying toolchain work that treats proofs as portable machine-checkable evidence [@leroy2009compcert; @necula1997proof].

Recent LLM-evaluation work also highlights inference nondeterminism from numerical precision and hardware configuration, reinforcing the value of proof-level claims whose validity does not depend on stochastic inference trajectories [@yuan2025fp32].

## Computational Decision Theory

The complexity of decision-making has been studied extensively. Foundational treatments of computational complexity and strategic decision settings establish the baseline used here [@papadimitriou1994complexity; @arora2009computational]. Our work extends this to the meta-question of identifying relevant information. Decision-theoretic and information-selection framing in this paper also sits in the tradition of statistical sufficiency and signaling/information economics [@fisher1922mathematical; @spence1973job; @myerson1979incentive; @milgrom1986price; @kamenica2011bayesian].

Large-sample Bayesian-network structure learning and causal identification are already known to be hard in adjacent formulations [@chickering2004large; @shpitser2006identification; @koller2009probabilistic]. Our object differs: we classify coordinate sufficiency for optimal-action invariance, with mechanized reductions and regime typing.

#### Relation to prior hardness results.

Closest adjacent results are feature-selection/model-selection hardness results for predictive subset selection [@blum1997selection; @amaldi1998complexity]. Relative to those works, this paper changes two formal objects: (i) the reductions are machine-checked (TAUTOLOGY and $\exists\forall$-SAT mappings with explicit polynomial bounds), and (ii) the output is a regime-typed hardness/tractability map for decision relevance under explicit encoding assumptions. The target predicate here is decision relevance, not predictive compression.

## Succinct Representations and Regime Separation

Representation-sensitive complexity is established in planning and decision-process theory: classical and compactly represented MDP/planning problems exhibit sharp complexity shifts under different input models [@papadimitriou1987mdp; @mundhenk2000mdp; @littman1998probplanning]. The explicit-vs-succinct separation in this paper is the same representation-sensitive phenomenon for the coordinate-sufficiency predicate.

The distinction in this paper is the object and scope of the classification: we classify *decision relevance* (sufficiency, anchor sufficiency, and minimum sufficient sets) for a fixed decision relation, with theorem-level regime typing and mechanized reduction chains.

## Oracle and Query-Access Lower Bounds

Query-access lower bounds are a standard source of computational hardness transfer [@dobzinski2012query; @buhrman2002complexity]. Our `[Q_fin]` and `[Q_bool]` results are in this tradition, but specialized to the same sufficiency predicate used throughout the paper: they establish access-obstruction lower bounds while keeping the underlying decision relation fixed across regimes.

Complementary companion work studies zero-error identification under constrained observation and proves rate-query lower bounds plus matroid structure of minimal distinguishing query sets [@simas2026identification]. Our object here is different: sufficiency of coordinates for optimal-action invariance in a decision problem, with coNP/$\Sigma_2^P$ classification and regime-typed transfer theorems.

## Energy Landscapes and Chemical Reaction Networks

The geometric interpretation of decision complexity connects to the physics of energy landscapes. Wales established a widely used picture in which molecular configurations form high-dimensional landscapes with basins and transition saddles [@wales2003energy; @wales2005energy; @wales2018exploring]. Protein-folding theory uses the same landscape language via funnel structure toward native states [@onuchic1997protein]. In this paper's formal model, the corresponding core object is coordinate-projection invariance of the optimizer map: sufficiency asks whether fixing coordinates preserves $\operatorname{Opt}$, while insufficiency is witnessed by agreeing projections with different optimal sets (Definition [\[def:sufficient\]](#def:sufficient){reference-type="ref" reference="def:sufficient"}, Proposition [\[prop:insufficiency-counterexample\]](#prop:insufficiency-counterexample){reference-type="ref" reference="prop:insufficiency-counterexample"}). \[D:Ddef:sufficient;Pprop:insufficiency-counterexample; R:DM\]

Under that mapping, the explicit-vs-succinct split is the mechanized statement of access asymmetry: \[E\] admits polynomial verification on explicit state access, while \[S+ETH\] admits worst-case exponential lower bounds on succinct inputs (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}); finite query access already exhibits indistinguishability barriers (Proposition [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"}). The complexity separation is mechanized. \[D:Tthm:dichotomy;Pprop:query-regime-obstruction; R:E,S+ETH,Q_fin\]

The geometric core is mechanized directly: product-space slice cardinality, hypercube node-count identity, and node-vs-edge separation are proved in Lean at the decision abstraction level, with edge witnesses tied exactly to non-sufficiency.

The circuit-to-decision instantiation is also mechanized in a separate bridge layer: geometry and dynamics are represented as typed components of a circuit object; decision circuits add an explicit interpretation layer; molecule-level constructors instantiate both views.

Chemical reaction networks provide a concrete physical class where this encoding applies directly. Prior work establishes hardness for output optimization, reconfiguration, and reconstruction in CRN settings [@andersen2012maximizing; @alaniz2023complexity; @flamml2013complexity]. Those domain-specific CRN complexity results are external literature claims, not mechanized in this Lean artifact. The mechanized statement here is the transfer principle: once a CRN decision task is encoded as a C1--C4 decision problem, it inherits the same sufficiency hardness/tractability regime map (Theorems [\[thm:config-reduction\]](#thm:config-reduction){reference-type="ref" reference="thm:config-reduction"}, [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}). \[D:Tthm:config-reduction, thm:sufficiency-conp, thm:tractable; R:E,S,TA\]

For matter-only dynamics, the law-induced objective specialization is mechanized for arbitrary universes (arbitrary state/action types and transition-feasibility relations): the utility schema is induced from transition laws, and under a strict allowed-vs-blocked gap with nonempty feasible set, the optimizer equals the feasible-action set; with logical determinism at the action layer, the optimizer is singleton.

The interface-time semantics are also explicit and mechanized: timed states are $\mathbb{N}$-indexed, one decision event is exactly one tick, run length equals elapsed interface time, and this unit-time law is invariant across substrate tags under interface-consistency assumptions. \[D:Pprop:time-discrete, prop:decision-unit-time, prop:run-time-accounting, prop:substrate-unit-time; R:AR\]

Regime-side interface machinery is also formalized as typed access objects with an explicit simulation preorder and certificate-upgrade statements. The access-channel and five-way composition theorems are encoded as assumption-explicit composition laws rather than informal metaphors.

## Thermodynamic Costs and Landauer's Principle

The thermodynamic lift in Section [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"} converts declared bit-operation lower bounds into declared energy/carbon lower bounds via linear conversion constants. In this artifact, those conversion consequences are mechanized conditionally through Propositions [\[prop:thermo-lift\]](#prop:thermo-lift){reference-type="ref" reference="prop:thermo-lift"}, [\[prop:thermo-hardness-bundle\]](#prop:thermo-hardness-bundle){reference-type="ref" reference="prop:thermo-hardness-bundle"}, [\[prop:thermo-mandatory-cost\]](#prop:thermo-mandatory-cost){reference-type="ref" reference="prop:thermo-mandatory-cost"}, and [\[prop:thermo-conservation-additive\]](#prop:thermo-conservation-additive){reference-type="ref" reference="prop:thermo-conservation-additive"}. Landauer's principle and reversible-computation context [@landauer1961irreversibility; @bennett2003notes] define the physical assumption set; the constants are declared premises, not Lean-derived constants. \[D:Pprop:thermo-lift, prop:thermo-hardness-bundle, prop:thermo-mandatory-cost, prop:thermo-conservation-additive; R:AR\]

Coupling this to integrity yields a mechanized policy condition: when exact competence is hardness-blocked in the declared regime, integrity requires abstention or explicitly weakened guarantees (Propositions [\[prop:integrity-resource-bound\]](#prop:integrity-resource-bound){reference-type="ref" reference="prop:integrity-resource-bound"}, [\[prop:attempted-competence-matrix\]](#prop:attempted-competence-matrix){reference-type="ref" reference="prop:attempted-competence-matrix"}). A stronger behavioral claim such as "abstention is globally utility-optimal for every objective" is *not* currently mechanized and remains objective-dependent. \[D:Pprop:integrity-resource-bound, prop:attempted-competence-matrix; R:AR\]

## Feature Selection

In machine learning, feature selection asks which input features are relevant for prediction. This is known to be NP-hard in general [@blum1997selection; @guyon2003introduction]. Our results show the decision-theoretic analog is coNP-complete for both checking and minimization.

## Value of Information

The value of information (VOI) framework [@howard1966information; @raiffa1961applied] quantifies the maximum rational payment for information. Our work addresses a different question: not the *value* of information, but the *complexity* of identifying which information has value.

## Model Selection

Statistical model selection (AIC/BIC/cross-validation) provides practical heuristics for choosing among models [@akaike1974new; @schwarz1978estimating; @stone1974cross]. Our results formalize the regime-level reason heuristic selection appears: without added structural assumptions, exact optimal model selection inherits worst-case intractability, so heuristic methods implement explicit weakened-guarantee policies for unresolved structure.

## Information Compression vs Certification Length

The paper now makes an explicit two-part information accounting object (Definition [\[def:raw-certified-bits\]](#def:raw-certified-bits){reference-type="ref" reference="def:raw-certified-bits"}): raw report bits and evidence-backed certification bits. This sharpens the information-theoretic reading of typed claims: compression of report payload is not equivalent to compression of certifiable truth conditions [@shannon1948mathematical; @cover2006elements; @slepian1973noiseless].

From a zero-error viewpoint, this distinction is structural rather than stylistic: compressed representations can remain short while exact decodability depends on confusability structure and admissible decoding conditions [@shannon1956zero; @korner1973graphs; @lovasz1979shannon; @csiszar2011information]. The same separation appears here between short reports and evidence-backed exact claims.

The rate-distortion and MDL lines make the same split in different language: there is a difference between achievable compression rate, computational procedure for obtaining/optimizing that rate, and certifiable model adequacy [@shannon1959coding; @blahut1972computation; @rissanen1978modeling; @grunwald2007minimum; @li2008introduction].

Formally, Theorem [\[thm:exact-certified-gap-iff-admissible\]](#thm:exact-certified-gap-iff-admissible){reference-type="ref" reference="thm:exact-certified-gap-iff-admissible"} and Corollary [\[cor:hardness-raw-only-exact\]](#cor:hardness-raw-only-exact){reference-type="ref" reference="cor:hardness-raw-only-exact"} characterize the exact-report boundary: admissible exact reports require a strict certified-bit gap above raw payload, while hardness-blocked exact reports collapse to raw-only accounting. This directly links representational succinctness to certification cost under the declared contract, rather than treating "short reports" as automatically high-information claims.

## Certifying Outputs and Proof-Carrying Claims

Our integrity layer matches the certifying-algorithms pattern: algorithms emit candidate outputs together with certificates that can be checked quickly, separating *producing* claims from *verifying* claims [@mcconnell2010certifying; @necula1997proof]. In this paper, Definition [\[def:solver-integrity\]](#def:solver-integrity){reference-type="ref" reference="def:solver-integrity"} is exactly that soundness discipline.

At the systems level, this is the same architecture as proof-carrying code: a producer ships evidence and a consumer runs a small checker before accepting the claim [@necula1997proof; @mcconnell2010certifying]. Our competence definition adds the regime-specific coverage/resource requirement that certifying soundness alone does not provide.

The feasibility qualifier in Definition [\[def:competence-regime\]](#def:competence-regime){reference-type="ref" reference="def:competence-regime"} yields the bounded-rationality constraint used in this paper: admissible policy is constrained by computational feasibility under the declared resource model (Remark [\[rem:modal-should\]](#rem:modal-should){reference-type="ref" reference="rem:modal-should"}) [@sep_bounded_rationality; @arora2009computational]. \[D:Pprop:integrity-competence-separation; R:AR\]

#### Cryptographic-verifiability perspective (scope).

The role of cryptography in this paper is structural verifiability, not secrecy: the relevant analogy is certificate-carrying claims with lightweight verification, not confidential encoding [@goldwasser1989knowledge; @necula1997proof]. Concretely, the typed-report discipline is modeled as a game-based reporting interface: a prover emits $(r,\pi)$ and a verifier accepts exactly when $\pi$ certifies the declared report type under the active contract. In that model, Evidence--Admissibility Equivalence gives completeness for admissible report types, while Typed Claim Admissibility plus Exact Claims Require Exact Evidence give soundness against exact overclaiming. Certified-confidence constraints then act as evidence-gated admissibility constraints on top of that verifier interface, so raw payload bits and certified bits represent distinct resources rather than stylistic notation variants.

#### Three-axis integration.

In the cited literature, these pillars are treated separately: representation-sensitive hardness, query-access lower bounds, and certifying soundness disciplines. This paper composes all three for the same decision-relevance object in one regime-typed and machine-checked framework.


# Conclusion

## Methodology and Disclosure {#methodology-and-disclosure .unnumbered}

**Role of LLMs in this work.** This paper was developed through human-AI collaboration. The author provided the core intuitions: the connection between decision-relevance and computational complexity, the conjecture that SUFFICIENCY-CHECK is coNP-complete, and the insight that the $\Sigma_{2}^{P}$ structure collapses for MINIMUM-SUFFICIENT-SET. Large language models (Claude, GPT-4) served as implementation partners for proof drafting, Lean formalization, and LaTeX generation.

The Lean 4 proofs were iteratively refined: the author specified the target statements, the LLM proposed proof strategies, and the Lean compiler served as the arbiter of correctness. The complexity-theoretic reductions required careful human oversight to ensure the polynomial bounds were correctly established.

**What the author contributed:** The problem formulations (SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, ANCHOR-SUFFICIENCY), the hardness conjectures, the tractability conditions, and the connection to over-modeling in engineering practice.

**What LLMs contributed:** LaTeX drafting, Lean tactic exploration, reduction construction assistance, and prose refinement.

The proofs are machine-checked; their validity is independent of generation method. This methodology is disclosed for academic transparency.

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

-   Discrete-time interface semantics are formalized: time is $\mathbb{N}$-valued, decision events are exactly one-tick transitions, run length equals elapsed time, and substrate-consistent realizations preserve the same one-unit event law (Propositions [\[prop:time-discrete\]](#prop:time-discrete){reference-type="ref" reference="prop:time-discrete"}--[\[prop:substrate-unit-time\]](#prop:substrate-unit-time){reference-type="ref" reference="prop:substrate-unit-time"})

These results place the problem of identifying decision-relevant coordinates at the first and second levels of the polynomial hierarchy.

Beyond classification, the paper contributes a formal claim-typing framework (Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"}): structural complexity is a property of the fixed decision question, while representational hardness is regime-conditional access cost. This is why encoding-regime changes can move practical hardness without changing the underlying semantics.

The reduction constructions and key equivalence theorems are machine-checked in Lean 4 (see Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} for proof listings). The formalization verifies that the TAUTOLOGY reduction correctly maps tautologies to sufficient coordinate sets; complexity classifications (coNP-completeness, $\Sigma_{2}^{P}$-completeness) follow by composition with standard complexity-theoretic results (TAUTOLOGY is coNP-complete, $\exists\forall$-SAT is $\Sigma_{2}^{P}$-complete). The strengthened gadget showing that non-tautologies yield instances with *all coordinates relevant* is also formalized.

## Complexity Characterization {#complexity-characterization .unnumbered}

The results provide precise complexity characterizations within the formal model:

1.  **Exact bounds.** SUFFICIENCY-CHECK is coNP-complete, both coNP-hard and in coNP.

2.  **Constructive reductions.** The reductions from TAUTOLOGY and $\exists\forall$-SAT are explicit and machine-checked.

3.  **Encoding-regime separation.** Under \[E\], SUFFICIENCY-CHECK is polynomial in $|S|$. Under \[S+ETH\], there exist succinct worst-case instances (with $k^*=n$) requiring $2^{\Omega(n)}$ time. Under \[Q_fin\], the Opt-oracle core has $\Omega(|S|)$ worst-case query complexity (Boolean instantiation $\Omega(2^n)$), and under \[Q_bool\] the value-entry/state-batch refinements preserve the obstruction with weighted-cost transfer closures.

## The Complexity Redistribution Corollary {#the-complexity-redistribution-corollary .unnumbered}

Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} develops a quantitative consequence: when a problem requires $k$ dimensions and a model handles only $j < k$ natively, the remaining $k - j$ dimensions must be handled externally at each decision site. For $n$ sites, total external work is $(k-j) \times n$. \[D:Tthm:tax-grows; R:LC\]

The set identity is elementary; its operational content comes from composition with the hardness results on exact relevance minimization. This redistribution corollary is formalized in Lean 4 (`HardnessDistribution.lean`), proving:

-   Redistribution identity: complexity burden cannot be eliminated by omission, only moved between native handling and external handling

-   Dominance: complete models have lower total work than incomplete models

-   Amortization: there exists a threshold $n^*$ beyond which higher-dimensional models have lower total cost

## Open Questions {#open-questions .unnumbered}

The landscape above is complete for the static sufficiency class under C1--C4 and the declared regimes; the items below are adjacent-class extensions or secondary refinements. Several questions remain for future work:

-   **Fixed-parameter tractability (primary):** Is SUFFICIENCY-CHECK FPT when parameterized by the minimal sufficient-set size $k^*$, or is it W\[2\]-hard under this parameterization?

-   **Sequential/stochastic bridge extension:** Characterize the exact frontier where adjacent sequential objectives reduce to the static class via Proposition [\[prop:one-step-bridge\]](#prop:one-step-bridge){reference-type="ref" reference="prop:one-step-bridge"}, and where genuinely new complexity objects (e.g., horizon/sample/regret complexity) must replace the present coNP/$\Sigma_2^P$ analysis.

-   **Average-case complexity:** What is the complexity under natural distributions on decision problems?

-   **Typed-confidence calibration:** For signaled reports $(r,g,p_{\mathrm{self}},p_{\mathrm{cert}})$, characterize proper scoring and calibration objectives that preserve signal consistency and typed admissibility.

-   **Learning cost formalization:** Can central cost $H_{\text{central}}$ be formalized as the rank of a concept matroid, making the amortization threshold precisely computable?

## Practical Corollaries {#practical-corollaries .unnumbered}

The practical corollaries are regime-indexed and theorem-indexed:

-   **\[E\] and structured regimes:** polynomial-time exact procedures exist (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

-   **\[Q_fin\]/\[Q_bool\] query-access lower bounds:** worst-case Opt-oracle complexity is $\Omega(|S|)$ in the finite-state core (Boolean instantiation $\Omega(2^n)$), and value-entry/state-batch interfaces satisfy the same obstruction in the mechanized Boolean refinement (Propositions [\[prop:query-regime-obstruction\]](#prop:query-regime-obstruction){reference-type="ref" reference="prop:query-regime-obstruction"}--[\[prop:oracle-lattice-strict\]](#prop:oracle-lattice-strict){reference-type="ref" reference="prop:oracle-lattice-strict"}), with randomized weighted robustness and oracle-lattice closures.

-   **\[S+ETH\] hard families:** exact minimization inherits exponential worst-case cost (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} together with Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}).

-   **\[S_bool\] mechanized criterion:** minimization reduces to relevance-cardinality constraints (Corollary [\[cor:practice-diagnostic\]](#cor:practice-diagnostic){reference-type="ref" reference="cor:practice-diagnostic"}).

-   **Redistribution consequences:** omitted native coverage externalizes work with explicit growth/amortization laws (Theorems [\[thm:tax-conservation\]](#thm:tax-conservation){reference-type="ref" reference="thm:tax-conservation"}--[\[thm:amortization\]](#thm:amortization){reference-type="ref" reference="thm:amortization"}).

Hence the design choice is typed: enforce a tractable regime, or adopt weakened guarantees with explicit verification boundaries. \[D:Tthm:tractable, thm:dichotomy; R:RG\] Equivalently, under the attempted-competence matrix, over-specification is rational only in attempted-competence-failure cells; once exact competence is available in the active regime (or no attempted exact competence was made), persistent over-specification is irrational for the same verified-cost objective. \[D:Pprop:attempted-competence-matrix; R:AR\] By Proposition [\[prop:attempted-competence-matrix\]](#prop:attempted-competence-matrix){reference-type="ref" reference="prop:attempted-competence-matrix"}, the integrity-preserving matrix contains 3 irrational cells and 1 rational cell. \[D:Pprop:attempted-competence-matrix; R:AR\]

## Epistemic Alignment Implications for Agent Training {#epistemic-alignment-implications-for-agent-training .unnumbered}

Within this paper's formalism, epistemic alignment is a claim-discipline property: outputs are asserted only when certifiable, and otherwise emitted as abstain reports (optionally carrying tentative guesses and self-reflected confidence under zero certified confidence). Formally, this is the integrity/competence split of Section [\[sec:interpretive-foundations\]](#sec:interpretive-foundations){reference-type="ref" reference="sec:interpretive-foundations"}, not a full value-alignment claim. \[D:Ddef:solver-integrity, def:competence-regime;Pprop:integrity-competence-separation; R:TR\]

#### Truth-Objective Abstention Requirement.

If a solver-agent declares a truth-preserving objective for claims about relation $\mathcal{R}$ in regime $\Gamma$, uncertified outputs are admissible only as $\mathsf{ABSTAIN}/\mathsf{UNKNOWN}$ rather than asserted answers. Under the signal discipline, this includes abstain-with-guess/self-confidence reports while keeping certification evidence-gated. \[D:Ddef:signaled-typed-report, def:signal-consistency;Pprop:certified-confidence-gate, prop:abstain-guess-self-signal;Ccor:exact-no-competence-zero-certified; R:AR\] Equivalently, training policies that suppress abstention in uncertified regions violate the typed claim discipline under the declared task model. \[D:Ddef:solver-integrity;Pprop:integrity-competence-separation, prop:integrity-resource-bound, prop:attempted-competence-matrix; R:AR\]

This yields a training doctrine for solver-agents under declared tasks/regimes:

1.  Treat $\mathsf{ABSTAIN}/\mathsf{UNKNOWN}$ as first-class admissible outputs, not errors. \[D:Ddef:solver-integrity; R:TR\]

2.  For signaled reports, maintain two channels: self-reflected confidence may be emitted, but certified confidence is positive only with evidence. \[D:Ddef:signal-consistency;Pprop:certified-confidence-gate, prop:self-confidence-not-certification; R:AR\]

3.  Treat runtime disclosure as scalar-witnessed: always emit exact step-count, and emit completion percentage only when a declared bound exists. \[D:Pprop:steps-run-scalar, prop:no-fraction-without-bound, prop:fraction-defined-under-bound; R:AR\]

4.  Optimize competent coverage subject to integrity constraints, rather than optimizing answer-rate alone. \[D:Ddef:competence-regime;Pprop:integrity-competence-separation; R:AR\]

5.  In hardness-blocked regimes, abstention or explicit guarantee-weakening is structurally required unless regime assumptions are changed. \[D:Tthm:dichotomy;Pprop:integrity-resource-bound, prop:attempted-competence-matrix; R:S,S+ETH\]

Operationally, a reporting schema consistent with this framework tracks at least five quantities: integrity violations, competent non-abstaining coverage on the declared scope, abstention quality under regime shift, the calibration gap between self-reflected and certified confidence channels, and scalar runtime witness distributions (with bound-qualified fraction semantics when bounds are declared). This is consistent with bounded-rationality feasibility discipline under declared resource models [@sep_bounded_rationality; @arora2009computational].


# Lean 4 Proof Listings {#app:lean}

The complete Lean 4 formalization is available in the companion artifact (Zenodo DOI listed on the title page). The mechanization consists of 11932 lines across 53 files, with 553 theorem/lemma statements.

**Handle IDs.** Inline theorem metadata now cites compact IDs (for example, `HD6`, `CC12`, `IC4`) instead of full theorem constants. The full ID-to-handle mapping is listed in Section [1.1](#sec:lean-handle-id-map){reference-type="ref" reference="sec:lean-handle-id-map"}.

## Lean Handle ID Map {#sec:lean-handle-id-map}

## What Is Machine-Checked

The Lean formalization establishes:

1.  **Correctness of the TAUTOLOGY reduction:** The theorem `tautology_iff_sufficient` proves that the mapping from Boolean formulas to decision problems preserves the decision structure (accept iff the formula is a tautology).

2.  **Decision problem definitions:** Formal definitions of sufficiency, optimality, and the decision quotient.

3.  **Economic theorems:** Simplicity Tax redistribution identities and hardness distribution results.

4.  **Query-access lower-bound core:** Formalized Boolean query-model indistinguishability theorem for the full problem via the $I=\emptyset$ subproblem (`emptySufficiency_query_indistinguishable_pair`), plus obstruction-scale identities (`queryComplexityLowerBound`, `exponential_query_complexity`).

**Complexity classifications** (coNP-completeness, $\Sigma_2^P$-completeness) follow by conditional composition with standard results (e.g., TAUTOLOGY coNP-completeness and $\exists\forall$-SAT $\Sigma_2^P$-completeness), represented explicitly as hypotheses in the conditional transfer theorems listed below. The Lean proofs verify the reduction constructions and the transfer closures under those hypotheses. The assumptions themselves are unpacked by an explicit ledger projection theorem () so dependency tracking is machine-auditable.

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


+-----------------------+--------------------------------------------------------------------------------------------------------+
| ID                    | Full Lean handle                                                                                       |
+:======================+:=======================================================================================================+
| ID                    | Full Lean handle (continued)                                                                           |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR1}         | `AccessRegime.le`                                                                                      |
| [AR1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR2}         | `AccessRegime.answer_space`                                                                            |
| [AR2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR3}         | `AccessRegime.le_refl`                                                                                 |
| [AR3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR4}         | `AccessRegime.le_trans`                                                                                |
| [AR4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AR5}         | `AccessRegime.query_space`                                                                             |
| [AR5]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AU1}         | `AdditiveUtility.isRelevant`                                                                           |
| [AU1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AU2}         | `AdditiveUtility.relevantSet`                                                                          |
| [AU2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:AU3}         | `AdditiveUtility.toProblem`                                                                            |
| [AU3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:BC1}         | `BooleanCircuit.circuitSize`                                                                           |
| [BC1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C1}          | `Complexity.BitStr`                                                                                    |
| [C1]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C2}          | `Complexity.Decides`                                                                                   |
| [C2]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C3}          | `Complexity.KarpReduces`                                                                               |
| [C3]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C4}          | `Complexity.Lang`                                                                                      |
| [C4]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C5}          | `Complexity.ManyOneReducesPoly`                                                                        |
| [C5]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C6}          | `Complexity.P`                                                                                         |
| [C6]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C7}          | `Complexity.PolyTime`                                                                                  |
| [C7]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C8}          | `Complexity.bitEnc`                                                                                    |
| [C8]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C9}          | `Counted.bind`                                                                                         |
| [C9]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C10}         | `Counted.bind_steps`                                                                                   |
| [C10]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C11}         | `Counted.pure`                                                                                         |
| [C11]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C12}         | `Counted.pure_steps`                                                                                   |
| [C12]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C13}         | `Counted.result`                                                                                       |
| [C13]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C14}         | `Counted.steps`                                                                                        |
| [C14]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C15}         | `Counted.steps_eq_fst`                                                                                 |
| [C15]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C16}         | `Counted.tick`                                                                                         |
| [C16]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C17}         | `Counted.tick_bind_steps`                                                                              |
| [C17]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:C31}         | `Clause3.eval`                                                                                         |
| [C31]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC1}         | `DecisionQuotient.ClaimClosure.RegimeSimulation`                                                       |
| [CC1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC2}         | `DecisionQuotient.ClaimClosure.adq_ordering`                                                           |
| [CC2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC3}         | `DecisionQuotient.ClaimClosure.agent_transfer_licensed_iff_snapshot`                                   |
| [CC3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC4}         | `DecisionQuotient.ClaimClosure.anchor_sigma2p_complete_conditional`                                    |
| [CC4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC5}         | `DecisionQuotient.ClaimClosure.anchor_sigma2p_reduction_core`                                          |
| [CC5]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC6}         | `DecisionQuotient.ClaimClosure.boundaryCharacterized_iff_exists_sufficient_subset`                     |
| [CC6]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC7}         | `DecisionQuotient.ClaimClosure.bounded_actions_detectable`                                             |
| [CC7]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC8}         | `DecisionQuotient.ClaimClosure.bridge_boundary_represented_family`                                     |
| [CC8]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC9}         | `DecisionQuotient.ClaimClosure.bridge_failure_witness_non_one_step`                                    |
| [CC9]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC10}        | `DecisionQuotient.ClaimClosure.bridge_transfer_iff_one_step_class`                                     |
| [CC10]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC11}        | `DecisionQuotient.ClaimClosure.certified_total_bits_split_core`                                        |
| [CC11]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC12}        | `DecisionQuotient.ClaimClosure.cost_asymmetry_eth_conditional`                                         |
| [CC12]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC13}        | `DecisionQuotient.ClaimClosure.declaredBudgetSlice`                                                    |
| [CC13]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC14}        | `DecisionQuotient.ClaimClosure.declaredRegimeFamily_complete`                                          |
| [CC14]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC15}        | `DecisionQuotient.ClaimClosure.declared_physics_no_universal_exact_certifier_core`                     |
| [CC15]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC16}        | `DecisionQuotient.ClaimClosure.dichotomy_conditional`                                                  |
| [CC16]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC17}        | `DecisionQuotient.ClaimClosure.epsilon_admissible_iff_raw_lt_certified_total_core`                     |
| [CC17]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC18}        | `DecisionQuotient.ClaimClosure.exact_admissible_iff_raw_lt_certified_total_core`                       |
| [CC18]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC19}        | `DecisionQuotient.ClaimClosure.exact_certainty_inflation_under_hardness_core`                          |
| [CC19]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC20}        | `DecisionQuotient.ClaimClosure.exact_raw_eq_certified_iff_certainty_inflation_core`                    |
| [CC20]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC21}        | `DecisionQuotient.ClaimClosure.exact_raw_only_of_no_exact_admissible_core`                             |
| [CC21]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC22}        | `DecisionQuotient.ClaimClosure.explicit_assumptions_required_of_not_excused_core`                      |
| [CC22]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC23}        | `DecisionQuotient.ClaimClosure.explicit_state_upper_core`                                              |
| [CC23]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC24}        | `DecisionQuotient.ClaimClosure.hard_family_all_coords_core`                                            |
| [CC24]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC25}        | `DecisionQuotient.ClaimClosure.horizonTwoWitness_immediate_empty_sufficient`                           |
| [CC25]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC26}        | `DecisionQuotient.ClaimClosure.horizon_gt_one_bridge_can_fail_on_sufficiency`                          |
| [CC26]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC27}        | `DecisionQuotient.ClaimClosure.information_barrier_opt_oracle_core`                                    |
| [CC27]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC28}        | `DecisionQuotient.ClaimClosure.information_barrier_state_batch_core`                                   |
| [CC28]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC29}        | `DecisionQuotient.ClaimClosure.information_barrier_value_entry_core`                                   |
| [CC29]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC30}        | `DecisionQuotient.ClaimClosure.integrity_resource_bound_for_sufficiency`                               |
| [CC30]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC31}        | `DecisionQuotient.ClaimClosure.integrity_universal_applicability_core`                                 |
| [CC31]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC32}        | `DecisionQuotient.ClaimClosure.meta_coordinate_irrelevant_of_invariance_on_declared_slice`             |
| [CC32]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC33}        | `DecisionQuotient.ClaimClosure.meta_coordinate_not_relevant_on_declared_slice`                         |
| [CC33]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC34}        | `DecisionQuotient.ClaimClosure.minsuff_collapse_core`                                                  |
| [CC34]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC36}        | `DecisionQuotient.ClaimClosure.minsuff_conp_complete_conditional`                                      |
| [CC36]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC37}        | `DecisionQuotient.ClaimClosure.no_auto_minimize_of_p_neq_conp`                                         |
| [CC37]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC38}        | `DecisionQuotient.ClaimClosure.no_exact_claim_admissible_under_hardness_core`                          |
| [CC38]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC39}        | `DecisionQuotient.ClaimClosure.no_exact_claim_under_declared_assumptions_unless_excused_core`          |
| [CC39]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC40}        | `DecisionQuotient.ClaimClosure.no_exact_identifier_implies_not_boundary_characterized`                 |
| [CC40]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC41}        | `DecisionQuotient.ClaimClosure.no_uncertified_exact_claim_core`                                        |
| [CC41]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC42}        | `DecisionQuotient.ClaimClosure.one_step_bridge`                                                        |
| [CC42]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC43}        | `DecisionQuotient.ClaimClosure.oracle_lattice_transfer_as_regime_simulation`                           |
| [CC43]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC44}        | `DecisionQuotient.ClaimClosure.physical_crossover_above_cap_core`                                      |
| [CC44]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC45}        | `DecisionQuotient.ClaimClosure.physical_crossover_core`                                                |
| [CC45]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC46}        | `DecisionQuotient.ClaimClosure.physical_crossover_hardness_core`                                       |
| [CC46]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC47}        | `DecisionQuotient.ClaimClosure.physical_crossover_policy_core`                                         |
| [CC47]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC48}        | `DecisionQuotient.ClaimClosure.process_bridge_failure_witness`                                         |
| [CC48]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC49}        | `DecisionQuotient.ClaimClosure.query_obstruction_boolean_corollary`                                    |
| [CC49]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC50}        | `DecisionQuotient.ClaimClosure.query_obstruction_finite_state_core`                                    |
| [CC50]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC51}        | `DecisionQuotient.ClaimClosure.regime_core_claim_proved`                                               |
| [CC51]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC52}        | `DecisionQuotient.ClaimClosure.regime_simulation_transfers_hardness`                                   |
| [CC52]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC53}        | `DecisionQuotient.ClaimClosure.reusable_heuristic_of_detectable`                                       |
| [CC53]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC54}        | `DecisionQuotient.ClaimClosure.selectorSufficient_not_implies_setSufficient`                           |
| [CC54]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC55}        | `DecisionQuotient.ClaimClosure.separable_detectable`                                                   |
| [CC55]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC56}        | `DecisionQuotient.ClaimClosure.snapshot_vs_process_typed_boundary`                                     |
| [CC56]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC57}        | `DecisionQuotient.ClaimClosure.standard_assumption_ledger_unpack`                                      |
| [CC57]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC58}        | `DecisionQuotient.ClaimClosure.stochastic_objective_bridge_can_fail_on_sufficiency`                    |
| [CC58]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC59}        | `DecisionQuotient.ClaimClosure.subproblem_hardness_lifts_to_full`                                      |
| [CC59]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC60}        | `DecisionQuotient.ClaimClosure.subproblem_transfer_as_regime_simulation`                               |
| [CC60]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC61}        | `DecisionQuotient.ClaimClosure.sufficiency_conp_complete_conditional`                                  |
| [CC61]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC62}        | `DecisionQuotient.ClaimClosure.sufficiency_conp_reduction_core`                                        |
| [CC62]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC63}        | `DecisionQuotient.ClaimClosure.sufficiency_iff_dq_ratio`                                               |
| [CC63]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC64}        | `DecisionQuotient.ClaimClosure.sufficiency_iff_projectedOptCover_eq_opt`                               |
| [CC64]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC65}        | `DecisionQuotient.ClaimClosure.thermo_conservation_additive_core`                                      |
| [CC65]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC66}        | `DecisionQuotient.ClaimClosure.thermo_energy_carbon_lift_core`                                         |
| [CC66]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC67}        | `DecisionQuotient.ClaimClosure.thermo_eventual_lift_core`                                              |
| [CC67]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC68}        | `DecisionQuotient.ClaimClosure.thermo_hardness_bundle_core`                                            |
| [CC68]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC69}        | `DecisionQuotient.ClaimClosure.thermo_mandatory_cost_core`                                             |
| [CC69]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC70}        | `DecisionQuotient.ClaimClosure.tractable_bounded_core`                                                 |
| [CC70]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC71}        | `DecisionQuotient.ClaimClosure.tractable_separable_core`                                               |
| [CC71]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC72}        | `DecisionQuotient.ClaimClosure.tractable_subcases_conditional`                                         |
| [CC72]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC73}        | `DecisionQuotient.ClaimClosure.tractable_tree_core`                                                    |
| [CC73]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC74}        | `DecisionQuotient.ClaimClosure.transition_coupled_bridge_can_fail_on_sufficiency`                      |
| [CC74]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC75}        | `DecisionQuotient.ClaimClosure.tree_structure_detectable`                                              |
| [CC75]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC76}        | `DecisionQuotient.ClaimClosure.typed_claim_admissibility_core`                                         |
| [CC76]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CC77}        | `DecisionQuotient.ClaimClosure.typed_static_class_completeness`                                        |
| [CC77]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP1}        | `ComputableDecisionProblem.checkSufficiency`                                                           |
| [CDP1]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP2}        | `ComputableDecisionProblem.checkSufficiency_iff_abstract`                                              |
| [CDP2]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP3}        | `ComputableDecisionProblem.computeOpt`                                                                 |
| [CDP3]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP4}        | `ComputableDecisionProblem.computeOpt_eq_abstract`                                                     |
| [CDP4]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP5}        | `ComputableDecisionProblem.decisionEquivDec`                                                           |
| [CDP5]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP6}        | `ComputableDecisionProblem.decisionEquivDec_iff`                                                       |
| [CDP6]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP7}        | `ComputableDecisionProblem.decisionEquivDec_iff_abstract`                                              |
| [CDP7]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP8}        | `ComputableDecisionProblem.insufficiencyWitnesses`                                                     |
| [CDP8]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP9}        | `ComputableDecisionProblem.isOptimalDec`                                                               |
| [CDP9]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP10}       | `ComputableDecisionProblem.isOptimalDec_iff`                                                           |
| [CDP10]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP11}       | `ComputableDecisionProblem.isOptimalDec_iff_abstract`                                                  |
| [CDP11]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP12}       | `ComputableDecisionProblem.mem_computeOpt_iff`                                                         |
| [CDP12]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP13}       | `ComputableDecisionProblem.toAbstract`                                                                 |
| [CDP13]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CDP14}       | `ComputableDecisionProblem.verifyWitness`                                                              |
| [CDP14]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:CR1}         | `DecisionQuotient.ConfigReduction.config_sufficiency_iff_behavior_preserving`                          |
| [CR1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP1}         | `DecisionQuotient.DecisionProblem.minimalSufficient_iff_relevant`                                      |
| [DP1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP2}         | `DecisionQuotient.DecisionProblem.relevantSet_is_minimal`                                              |
| [DP2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP3}         | `DecisionQuotient.DecisionProblem.sufficient_implies_selectorSufficient`                               |
| [DP3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP4}         | `DecisionQuotient.ClaimClosure.DecisionProblem.epsOpt_zero_eq_opt`                                     |
| [DP4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP5}         | `DecisionQuotient.ClaimClosure.DecisionProblem.sufficient_iff_zeroEpsilonSufficient`                   |
| [DP5]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP6}         | `DecisionProblem.anchorSufficient`                                                                     |
| [DP6]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP7}         | `DecisionProblem.classMonotoneOn`                                                                      |
| [DP7]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP8}         | `DecisionProblem.constant_opt_all_sufficient`                                                          |
| [DP8]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP9}         | `DecisionProblem.DecisionEquiv`                                                                        |
| [DP9]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP10}        | `DecisionProblem.DecisionQuotientType`                                                                 |
| [DP10]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP11}        | `DecisionProblem.Opt`                                                                                  |
| [DP11]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP12}        | `DecisionProblem.OptQuotient`                                                                          |
| [DP12]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP13}        | `DecisionProblem.SelectedAction`                                                                       |
| [DP13]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP14}        | `DecisionProblem.decisionEquiv_refl`                                                                   |
| [DP14]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP15}        | `DecisionProblem.decisionEquiv_symm`                                                                   |
| [DP15]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP16}        | `DecisionProblem.decisionEquiv_trans`                                                                  |
| [DP16]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP17}        | `DecisionProblem.decisionSetoid`                                                                       |
| [DP17]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP18}        | `DecisionProblem.dominant_all_sufficient`                                                              |
| [DP18]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP19}        | `DecisionProblem.dominant_unique`                                                                      |
| [DP19]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP20}        | `DecisionProblem.edgeOnComplement`                                                                     |
| [DP20]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP21}        | `DecisionProblem.edgeOnComplement_iff_not_sufficient`                                                  |
| [DP21]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP22}        | `DecisionProblem.emptySet_not_sufficient_iff_exists_opt_difference`                                    |
| [DP22]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP23}        | `DecisionProblem.emptySet_sufficient_iff_constant`                                                     |
| [DP23]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP24}        | `DecisionProblem.epsOpt`                                                                               |
| [DP24]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP25}        | `DecisionProblem.epsOpt_zero_eq_opt`                                                                   |
| [DP25]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP26}        | `DecisionProblem.erase_of_not_mem`                                                                     |
| [DP26]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP27}        | `DecisionProblem.factors_implies_respects`                                                             |
| [DP27]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP28}        | `DecisionProblem.hasConstantOpt`                                                                       |
| [DP28]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP29}        | `DecisionProblem.hasConstantOpt'`                                                                      |
| [DP29]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP30}        | `DecisionProblem.hasDominant`                                                                          |
| [DP30]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP31}        | `DecisionProblem.irrelevant_iff_not_relevant`                                                          |
| [DP31]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP32}        | `DecisionProblem.isEpsilonSufficient`                                                                  |
| [DP32]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP33}        | `DecisionProblem.isIrrelevant`                                                                         |
| [DP33]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP34}        | `DecisionProblem.isMinimalSufficient`                                                                  |
| [DP34]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP35}        | `DecisionProblem.isMinimalSufficient'`                                                                 |
| [DP35]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP36}        | `DecisionProblem.isOptimal`                                                                            |
| [DP36]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP37}        | `DecisionProblem.isRelevant`                                                                           |
| [DP37]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP38}        | `DecisionProblem.isSelectorSufficient`                                                                 |
| [DP38]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP39}        | `DecisionProblem.isSufficient`                                                                         |
| [DP39]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP40}        | `DecisionProblem.isSufficientAt`                                                                       |
| [DP40]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP41}        | `DecisionProblem.isSufficientOnSet`                                                                    |
| [DP41]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP42}        | `DecisionProblem.minimalSufficient_all_relevant'`                                                      |
| [DP42]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP43}        | `DecisionProblem.minimalSufficient_eq_relevant'`                                                       |
| [DP43]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP44}        | `DecisionProblem.minimalSufficient_iff_relevant`                                                       |
| [DP44]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP45}        | `DecisionProblem.monotoneIn`                                                                           |
| [DP45]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP46}        | `DecisionProblem.nonnegativelyMonotoneCoord`                                                           |
| [DP46]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP47}        | `DecisionProblem.not_sufficient_iff_exists_counterexample`                                             |
| [DP47]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP48}        | `DecisionProblem.numOptClasses`                                                                        |
| [DP48]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP49}        | `DecisionProblem.numOptClasses_le`                                                                     |
| [DP49]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP50}        | `DecisionProblem.numOptClasses_pos`                                                                    |
| [DP50]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP51}        | `DecisionProblem.opt_eq_optQuotient_comp`                                                              |
| [DP51]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP52}        | `DecisionProblem.opt_factors_through_quotient`                                                         |
| [DP52]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP53}        | `DecisionProblem.preservesOpt`                                                                         |
| [DP53]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP54}        | `DecisionProblem.preservesOptStrong`                                                                   |
| [DP54]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP55}        | `DecisionProblem.quotientEntropy`                                                                      |
| [DP55]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP56}        | `DecisionProblem.quotientEntropy_nonneg`                                                               |
| [DP56]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP57}        | `DecisionProblem.quotientEntropy_zero_of_constant`                                                     |
| [DP57]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP58}        | `DecisionProblem.quotientMap`                                                                          |
| [DP58]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP59}        | `DecisionProblem.quotientMap_preservesOpt`                                                             |
| [DP59]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP60}        | `DecisionProblem.quotientSize`                                                                         |
| [DP60]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP61}        | `DecisionProblem.quotient_is_coarsest`                                                                 |
| [DP61]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP62}        | `DecisionProblem.quotient_represents_opt_equiv`                                                        |
| [DP62]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP63}        | `DecisionProblem.relevantSet`                                                                          |
| [DP63]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP64}        | `DecisionProblem.relevantSet_is_minimal`                                                               |
| [DP64]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP65}        | `DecisionProblem.relevant_necessary`                                                                   |
| [DP65]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP66}        | `DecisionProblem.sufficientSets`                                                                       |
| [DP66]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP67}        | `DecisionProblem.sufficientSets_principal'`                                                            |
| [DP67]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP68}        | `DecisionProblem.sufficientSets_upward`                                                                |
| [DP68]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP69}        | `DecisionProblem.sufficientSets_upward_closed`                                                         |
| [DP69]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP70}        | `DecisionProblem.sufficient_contains_all_relevant`                                                     |
| [DP70]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP71}        | `DecisionProblem.sufficient_contains_relevant`                                                         |
| [DP71]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP72}        | `DecisionProblem.sufficient_erase_irrelevant'`                                                         |
| [DP72]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP73}        | `DecisionProblem.sufficient_iff_zeroEpsilonSufficient`                                                 |
| [DP73]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP74}        | `DecisionProblem.sufficient_implies_selectorSufficient`                                                |
| [DP74]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP75}        | `DecisionProblem.sufficient_superset`                                                                  |
| [DP75]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DP76}        | `DecisionProblem.univ_sufficient_of_injective`                                                         |
| [DP76]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ3}         | `DecisionQuotient.card_anchoredSlice_eq_pow_sub`                                                       |
| [DQ3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ5}         | `DecisionQuotient.opt_eq_feasible_of_gap`                                                              |
| [DQ5]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ6}         | `DecisionQuotient.opt_eq_of_allowed_iff`                                                               |
| [DQ6]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ7}         | `DecisionQuotient.opt_singleton_of_logicallyDeterministic`                                             |
| [DQ7]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ8}         | `DecisionQuotient.universe_sets_objective_schema`                                                      |
| [DQ8]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ9}         | `DecisionQuotient.AdditiveUtility`                                                                     |
| [DQ9]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ10}        | `DecisionQuotient.AssignX`                                                                             |
| [DQ10]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ11}        | `DecisionQuotient.AssignY`                                                                             |
| [DQ11]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ12}        | `DecisionQuotient.Assignment`                                                                          |
| [DQ12]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ13}        | `DecisionQuotient.BinaryState`                                                                         |
| [DQ13]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ14}        | `DecisionQuotient.BooleanCircuit`                                                                      |
| [DQ14]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ15}        | `DecisionQuotient.CircuitDecisionProblem`                                                              |
| [DQ15]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ16}        | `DecisionQuotient.ClaimClosure.agreeOn_refl`                                                           |
| [DQ16]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ17}        | `DecisionQuotient.ClaimClosure.agreeOn_symm`                                                           |
| [DQ17]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ18}        | `DecisionQuotient.ClaimClosure.agreeOn_trans`                                                          |
| [DQ18]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ19}        | `DecisionQuotient.ClaimClosure.irrelevantOn_implies_not_relevantOn`                                    |
| [DQ19]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ20}        | `DecisionQuotient.ClaimClosure.isIrrelevantOn`                                                         |
| [DQ20]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ21}        | `DecisionQuotient.ClaimClosure.isRelevantOn`                                                           |
| [DQ21]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ22}        | `DecisionQuotient.Clause3`                                                                             |
| [DQ22]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ23}        | `DecisionQuotient.ComputableDecisionProblem`                                                           |
| [DQ23]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ24}        | `DecisionQuotient.ConfigReduction.ConfigAction`                                                        |
| [DQ24]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ25}        | `DecisionQuotient.ConfigReduction.behaviorPreserving`                                                  |
| [DQ25]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ26}        | `DecisionQuotient.ConfigReduction.configDecisionProblem`                                               |
| [DQ26]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ27}        | `DecisionQuotient.ConfigReduction.configUtility`                                                       |
| [DQ27]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ28}        | `DecisionQuotient.ConfigReduction.configUtility_le_one`                                                |
| [DQ28]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ29}        | `DecisionQuotient.ConfigReduction.no_occurs_iff_of_behaviorPreserving`                                 |
| [DQ29]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ30}        | `DecisionQuotient.ConfigReduction.none_mem_Opt_iff_no_occurs`                                          |
| [DQ30]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ31}        | `DecisionQuotient.ConfigReduction.some_mem_Opt_iff_occurs`                                             |
| [DQ31]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ32}        | `DecisionQuotient.ConfigReduction.some_mem_Opt_of_occurs`                                              |
| [DQ32]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ33}        | `DecisionQuotient.ConfigReduction.some_not_mem_Opt_of_not_occurs`                                      |
| [DQ33]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ34}        | `DecisionQuotient.CoordinateSpace`                                                                     |
| [DQ34]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ35}        | `DecisionQuotient.Counted`                                                                             |
| [DQ35]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ36}        | `DecisionQuotient.DQAction`                                                                            |
| [DQ36]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ37}        | `DecisionQuotient.DQInstance`                                                                          |
| [DQ37]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ38}        | `DecisionQuotient.DecisionProblem`                                                                     |
| [DQ38]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ39}        | `DecisionQuotient.EncodedDecisionProblem`                                                              |
| [DQ39]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ40}        | `DecisionQuotient.ExistsForallFormula`                                                                 |
| [DQ40]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ41}        | `DecisionQuotient.ExistsForallFormula.embedVar`                                                        |
| [DQ41]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ42}        | `DecisionQuotient.ExistsForallFormula.eval_padUniversal`                                               |
| [DQ42]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ43}        | `DecisionQuotient.ExistsForallFormula.padUniversal`                                                    |
| [DQ43]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ44}        | `DecisionQuotient.ExistsForallFormula.restrictY`                                                       |
| [DQ44]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ45}        | `DecisionQuotient.ExistsForallFormula.satisfiable`                                                     |
| [DQ45]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ46}        | `DecisionQuotient.ExistsForallFormula.satisfiable_iff_padUniversal`                                    |
| [DQ46]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ47}        | `DecisionQuotient.ExistsForallFormula.satisfiedBy`                                                     |
| [DQ47]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ48}        | `DecisionQuotient.ExistsForallFormula.sumAssignment`                                                   |
| [DQ48]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ49}        | `DecisionQuotient.ExistsForallFormula.sumAssignment_embed`                                             |
| [DQ49]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ50}        | `DecisionQuotient.FiniteDecisionProblem`                                                               |
| [DQ50]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ51}        | `DecisionQuotient.FiniteDecisionProblem.decisionQuotient`                                              |
| [DQ51]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ52}        | `DecisionQuotient.FiniteDecisionProblem.isSufficient`                                                  |
| [DQ52]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ53}        | `DecisionQuotient.FiniteDecisionProblem.isSufficient_superset`                                         |
| [DQ53]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ54}        | `DecisionQuotient.FiniteDecisionProblem.mem_optimalActions_iff`                                        |
| [DQ54]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ55}        | `DecisionQuotient.FiniteDecisionProblem.optimalActions`                                                |
| [DQ55]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ56}        | `DecisionQuotient.FiniteDecisionProblem.optimalActions_subset_actions`                                 |
| [DQ56]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ57}        | `DecisionQuotient.FiniteDecisionProblem.toDecisionProblem`                                             |
| [DQ57]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ58}        | `DecisionQuotient.HardnessDistribution.IsEventuallyConstant`                                           |
| [DQ58]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ59}        | `DecisionQuotient.HardnessDistribution.SolutionArchitecture`                                           |
| [DQ59]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ60}        | `DecisionQuotient.HardnessDistribution.SpecificationProblem`                                           |
| [DQ60]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ61}        | `DecisionQuotient.HardnessDistribution.amortizationThreshold`                                          |
| [DQ61]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ62}        | `DecisionQuotient.HardnessDistribution.amortization_threshold_native_manual`                           |
| [DQ62]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ63}        | `DecisionQuotient.HardnessDistribution.centralization_step_reduces_total`                              |
| [DQ63]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ64}        | `DecisionQuotient.HardnessDistribution.centralized_constant`                                           |
| [DQ64]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ65}        | `DecisionQuotient.HardnessDistribution.centralized_minimal_errors`                                     |
| [DQ65]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ66}        | `DecisionQuotient.HardnessDistribution.distributed_errors_grow`                                        |
| [DQ66]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ67}        | `DecisionQuotient.HardnessDistribution.distributed_multiplies`                                         |
| [DQ67]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ68}        | `DecisionQuotient.HardnessDistribution.dof_conservation`                                               |
| [DQ68]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ69}        | `DecisionQuotient.HardnessDistribution.errorSites`                                                     |
| [DQ69]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ70}        | `DecisionQuotient.HardnessDistribution.gapCard`                                                        |
| [DQ70]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ71}        | `DecisionQuotient.HardnessDistribution.generalizedTotalDOF`                                            |
| [DQ71]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ72}        | `DecisionQuotient.HardnessDistribution.generalized_right_dominates_wrong_pointwise`                    |
| [DQ72]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ73}        | `DecisionQuotient.HardnessDistribution.hardnessEfficiency`                                             |
| [DQ73]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ74}        | `DecisionQuotient.HardnessDistribution.less_distributed_less_total`                                    |
| [DQ74]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ75}        | `DecisionQuotient.HardnessDistribution.leverageRatio`                                                  |
| [DQ75]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ76}        | `DecisionQuotient.HardnessDistribution.linear_lt_exponential_eventually`                               |
| [DQ76]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ77}        | `DecisionQuotient.HardnessDistribution.linear_represents_saturating_only_zero_slope`                   |
| [DQ77]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ78}        | `DecisionQuotient.HardnessDistribution.manualApproach`                                                 |
| [DQ78]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ79}        | `DecisionQuotient.HardnessDistribution.manual_errors_grow`                                             |
| [DQ79]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ80}        | `DecisionQuotient.HardnessDistribution.manual_is_wrong`                                                |
| [DQ80]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ81}        | `DecisionQuotient.HardnessDistribution.nativeTypeSystem`                                               |
| [DQ81]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ82}        | `DecisionQuotient.HardnessDistribution.native_is_right`                                                |
| [DQ82]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ83}        | `DecisionQuotient.HardnessDistribution.native_minimal_errors`                                          |
| [DQ83]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ84}        | `DecisionQuotient.HardnessDistribution.right_fewer_error_sites`                                        |
| [DQ84]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ85}        | `DecisionQuotient.HardnessDistribution.saturatingSiteCost`                                             |
| [DQ85]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ86}        | `DecisionQuotient.HardnessDistribution.simplicityTax`                                                  |
| [DQ86]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ87}        | `DecisionQuotient.HardnessDistribution.simplicityTax_conservation`                                     |
| [DQ87]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ88}        | `DecisionQuotient.HardnessDistribution.totalDOF`                                                       |
| [DQ88]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ89}        | `DecisionQuotient.HardnessDistribution.totalDOF_eventually_constant_of_zero_distributed`               |
| [DQ89]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ90}        | `DecisionQuotient.HardnessDistribution.totalExternalWork`                                              |
| [DQ90]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ91}        | `DecisionQuotient.HardnessDistribution.totalExternalWork_eq_n_mul_gapCard`                             |
| [DQ91]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ92}        | `DecisionQuotient.HardnessDistribution.zero_distributed_of_totalDOF_eventually_constant`               |
| [DQ92]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ93}        | `DecisionQuotient.InP`                                                                                 |
| [DQ93]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ94}        | `DecisionQuotient.InsufficiencyWitness`                                                                |
| [DQ94]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ95}        | `DecisionQuotient.IntegrityCompetence.CertifyingSolver`                                                |
| [DQ95]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ96}        | `DecisionQuotient.IntegrityCompetence.ClaimAdmissible`                                                 |
| [DQ96]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ97}        | `DecisionQuotient.IntegrityCompetence.CompetentOn`                                                     |
| [DQ97]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ98}        | `DecisionQuotient.IntegrityCompetence.EpsilonCompetentOn`                                              |
| [DQ98]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ99}        | `DecisionQuotient.IntegrityCompetence.EpsilonRelation`                                                 |
| [DQ99]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ100}       | `DecisionQuotient.IntegrityCompetence.Regime`                                                          |
| [DQ100]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ101}       | `DecisionQuotient.IntegrityCompetence.SolverIntegrity`                                                 |
| [DQ101]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ102}       | `DecisionQuotient.IntegrityCompetence.admissibleIrrationalCount`                                       |
| [DQ102]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ103}       | `DecisionQuotient.IntegrityCompetence.admissibleRationalCount`                                         |
| [DQ103]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ104}       | `DecisionQuotient.IntegrityCompetence.admissible_epsilon_implies_integrity`                            |
| [DQ104]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ105}       | `DecisionQuotient.IntegrityCompetence.admissible_exact_implies_integrity`                              |
| [DQ105]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ106}       | `DecisionQuotient.IntegrityCompetence.alwaysAbstain`                                                   |
| [DQ106]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ107}       | `DecisionQuotient.IntegrityCompetence.alwaysAbstain_integrity`                                         |
| [DQ107]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ108}       | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_eq_raw_plus_overhead`                         |
| [DQ108]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ109}       | `DecisionQuotient.IntegrityCompetence.claim_admissible_abstain`                                        |
| [DQ109]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ110}       | `DecisionQuotient.IntegrityCompetence.claim_admissible_epsilon_iff`                                    |
| [DQ110]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ111}       | `DecisionQuotient.IntegrityCompetence.claim_admissible_exact_iff`                                      |
| [DQ111]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ112}       | `DecisionQuotient.IntegrityCompetence.competent_has_coverage`                                          |
| [DQ112]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ113}       | `DecisionQuotient.IntegrityCompetence.epsilon_admissible_iff_raw_lt_certifiedTotal`                    |
| [DQ113]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ114}       | `DecisionQuotient.IntegrityCompetence.exact_admissible_iff_raw_lt_certifiedTotal`                      |
| [DQ114]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ115}       | `DecisionQuotient.IntegrityCompetence.exact_raw_eq_certifiedTotal_iff_exactCertaintyInflation`         |
| [DQ115]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ116}       | `DecisionQuotient.IntegrityCompetence.inducedRelation`                                                 |
| [DQ116]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ117}       | `DecisionQuotient.IntegrityCompetence.no_uncertified_epsilon_claim`                                    |
| [DQ117]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ118}       | `DecisionQuotient.IntegrityCompetence.no_uncertified_exact_claim`                                      |
| [DQ118]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ119}       | `DecisionQuotient.IntegrityCompetence.overModelVerdict`                                                |
| [DQ119]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ120}       | `DecisionQuotient.IntegrityCompetence.overModelVerdict_inadmissible_iff`                               |
| [DQ120]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ121}       | `DecisionQuotient.IntegrityCompetence.overModelVerdict_irrational_iff`                                 |
| [DQ121]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ122}       | `DecisionQuotient.IntegrityCompetence.program_framed_as_solver`                                        |
| [DQ122]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ123}       | `DecisionQuotient.IntegrityCompetence.report_admissible_implies_raw_lt_certifiedTotal`                 |
| [DQ123]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ124}       | `DecisionQuotient.IntegrityCompetence.report_not_admissible_implies_raw_eq_certifiedTotal`             |
| [DQ124]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ125}       | `DecisionQuotient.IntegrityCompetence.report_raw_eq_certifiedTotal_iff_certaintyInflation`             |
| [DQ125]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ126}       | `DecisionQuotient.IntegrityCompetence.rlffReward_abstain`                                              |
| [DQ126]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ127}       | `DecisionQuotient.IntegrityCompetence.rlffReward_of_evidence`                                          |
| [DQ127]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ128}       | `DecisionQuotient.IntegrityCompetence.rlffReward_of_no_evidence`                                       |
| [DQ128]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ129}       | `DecisionQuotient.IntegrityCompetence.solverIntegrity_substrate_parametric`                            |
| [DQ129]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ130}       | `DecisionQuotient.IntegrityCompetence.solverOfPartialMap`                                              |
| [DQ130]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ131}       | `DecisionQuotient.IntegrityCompetence.solverOfPartialMap_integrity`                                    |
| [DQ131]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ132}       | `DecisionQuotient.IntegrityCompetence.steps_run_scalar_always_defined`                                 |
| [DQ132]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ133}       | `DecisionQuotient.IntegrityCompetence.steps_run_scalar_falsifiable`                                    |
| [DQ133]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ134}       | `DecisionQuotient.IntegrityCompetence.zero_epsilon_competence_iff_exact`                               |
| [DQ134]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ135}       | `DecisionQuotient.InteriorVerification.CoordScore`                                                     |
| [DQ135]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ136}       | `DecisionQuotient.InteriorVerification.not_sufficientOnSet_of_counterexample`                          |
| [DQ136]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ137}       | `DecisionQuotient.InteriorVerification.singleton_coordinate_interior_certificate`                      |
| [DQ137]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ138}       | `DecisionQuotient.IsPolynomialTime`                                                                    |
| [DQ138]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ139}       | `DecisionQuotient.Literal`                                                                             |
| [DQ139]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ140}       | `DecisionQuotient.MinSufficientSetInstance`                                                            |
| [DQ140]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ141}       | `DecisionQuotient.Outside`                                                                             |
| [DQ141]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ142}       | `DecisionQuotient.PhysicalBudgetCrossover.EncodingSizeModel`                                           |
| [DQ142]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ143}       | `DecisionQuotient.PhysicalBudgetCrossover.ExplicitInfeasible`                                          |
| [DQ143]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ144}       | `DecisionQuotient.PhysicalBudgetCrossover.ExplicitUnbounded`                                           |
| [DQ144]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ145}       | `DecisionQuotient.PhysicalBudgetCrossover.HasCrossover`                                                |
| [DQ145]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ146}       | `DecisionQuotient.PhysicalBudgetCrossover.SuccinctBoundedBy`                                           |
| [DQ146]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ147}       | `DecisionQuotient.PhysicalBudgetCrossover.SuccinctFeasible`                                            |
| [DQ147]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ148}       | `DecisionQuotient.PhysicalBudgetCrossover.crossover_for_all_budgets_above_cap`                         |
| [DQ148]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ149}       | `DecisionQuotient.PhysicalBudgetCrossover.crossover_hardness_bundle`                                   |
| [DQ149]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ150}       | `DecisionQuotient.PhysicalBudgetCrossover.crossover_integrity_policy`                                  |
| [DQ150]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ151}       | `DecisionQuotient.PhysicalBudgetCrossover.has_crossover_of_bounded_succinct_unbounded_explicit`        |
| [DQ151]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ152}       | `DecisionQuotient.PhysicalBudgetCrossover.has_crossover_of_witness`                                    |
| [DQ152]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ153}       | `DecisionQuotient.Physics.Instantiation.Configuration`                                                 |
| [DQ153]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ154}       | `DecisionQuotient.Physics.Instantiation.DecisionCircuit`                                               |
| [DQ154]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ155}       | `DecisionQuotient.Physics.Instantiation.DecisionInterpretation`                                        |
| [DQ155]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ156}       | `DecisionQuotient.Physics.Instantiation.EnergyLandscape`                                               |
| [DQ156]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ157}       | `DecisionQuotient.Physics.Instantiation.LandauerBound`                                                 |
| [DQ157]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ158}       | `DecisionQuotient.Physics.Instantiation.Molecule`                                                      |
| [DQ158]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ159}       | `DecisionQuotient.Physics.Instantiation.MoleculeAsCircuit`                                             |
| [DQ159]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ160}       | `DecisionQuotient.Physics.Instantiation.MoleculeAsDecisionCircuit`                                     |
| [DQ160]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ162}       | `DecisionQuotient.Physics.Instantiation.Reaction`                                                      |
| [DQ162]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ163}       | `DecisionQuotient.Physics.Instantiation.k_Boltzmann`                                                   |
| [DQ163]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ164}       | `DecisionQuotient.PolyReduction`                                                                       |
| [DQ164]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ165}       | `DecisionQuotient.PolyTimeApprox`                                                                      |
| [DQ165]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ166}       | `DecisionQuotient.PolytimeElicitationMechanism`                                                        |
| [DQ166]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ167}       | `DecisionQuotient.Prior`                                                                               |
| [DQ167]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ168}       | `DecisionQuotient.ProductSpace`                                                                        |
| [DQ168]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ169}       | `DecisionQuotient.QBFState`                                                                            |
| [DQ169]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ170}       | `DecisionQuotient.QueryAlgorithm`                                                                      |
| [DQ170]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ171}       | `DecisionQuotient.QueryTranscript`                                                                     |
| [DQ171]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ172}       | `DecisionQuotient.SAT3Instance`                                                                        |
| [DQ172]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ173}       | `DecisionQuotient.SAT3Instance.eval`                                                                   |
| [DQ173]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ174}       | `DecisionQuotient.SAT3Instance.eval_eq_true_iff`                                                       |
| [DQ174]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ175}       | `DecisionQuotient.SAT3Instance.satisfiable`                                                            |
| [DQ175]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ176}       | `DecisionQuotient.SAT3Instance.satisfiedBy`                                                            |
| [DQ176]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ177}       | `DecisionQuotient.SeparableUtility`                                                                    |
| [DQ177]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ178}       | `DecisionQuotient.SetComparisonInstance`                                                               |
| [DQ178]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ179}       | `DecisionQuotient.SharpSATInstance`                                                                    |
| [DQ179]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ180}       | `DecisionQuotient.Sigma2PHardness.GadgetState`                                                         |
| [DQ180]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ181}       | `DecisionQuotient.Sigma2PHardness.I_eq_I_of_encodeX`                                                   |
| [DQ181]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ182}       | `DecisionQuotient.Sigma2PHardness.I_of_encodeX_subset`                                                 |
| [DQ182]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ183}       | `DecisionQuotient.Sigma2PHardness.I_of_x`                                                              |
| [DQ183]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ184}       | `DecisionQuotient.Sigma2PHardness.I_of_x_card`                                                         |
| [DQ184]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ185}       | `DecisionQuotient.Sigma2PHardness.bit`                                                                 |
| [DQ185]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ186}       | `DecisionQuotient.Sigma2PHardness.bit_le_one`                                                          |
| [DQ186]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ187}       | `DecisionQuotient.Sigma2PHardness.bit_lt_two`                                                          |
| [DQ187]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ188}       | `DecisionQuotient.Sigma2PHardness.cCoord`                                                              |
| [DQ188]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ189}       | `DecisionQuotient.Sigma2PHardness.cCoord_inj`                                                          |
| [DQ189]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ190}       | `DecisionQuotient.Sigma2PHardness.cCoord_inj_bits`                                                     |
| [DQ190]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ191}       | `DecisionQuotient.Sigma2PHardness.cCoord_injective`                                                    |
| [DQ191]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ192}       | `DecisionQuotient.Sigma2PHardness.cCoord_val`                                                          |
| [DQ192]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ193}       | `DecisionQuotient.Sigma2PHardness.cCoord_val_lt_of_lt`                                                 |
| [DQ193]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ194}       | `DecisionQuotient.Sigma2PHardness.disjoint_I_of_x00_x11`                                               |
| [DQ194]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ195}       | `DecisionQuotient.Sigma2PHardness.encodeX`                                                             |
| [DQ195]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ196}       | `DecisionQuotient.Sigma2PHardness.encodeX_I_of_x`                                                      |
| [DQ196]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ197}       | `DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant`                                           |
| [DQ197]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ198}       | `DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant_iff_mem_relevant`                          |
| [DQ198]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ199}       | `DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant_implies_representationGap_zero`            |
| [DQ199]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ200}       | `DecisionQuotient.Sigma2PHardness.goodEq`                                                              |
| [DQ200]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ201}       | `DecisionQuotient.Sigma2PHardness.goodEq_x00`                                                          |
| [DQ201]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ202}       | `DecisionQuotient.Sigma2PHardness.goodEq_x11`                                                          |
| [DQ202]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ203}       | `DecisionQuotient.Sigma2PHardness.mem_I_of_x_iff`                                                      |
| [DQ203]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ204}       | `DecisionQuotient.Sigma2PHardness.mem_relevantFinset_iff`                                              |
| [DQ204]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ205}       | `DecisionQuotient.Sigma2PHardness.not_goodEq_x01`                                                      |
| [DQ205]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ206}       | `DecisionQuotient.Sigma2PHardness.not_sufficient_of_missing_relevantFinset`                            |
| [DQ206]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ207}       | `DecisionQuotient.Sigma2PHardness.relevantFinset`                                                      |
| [DQ207]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ208}       | `DecisionQuotient.Sigma2PHardness.representationGap`                                                   |
| [DQ208]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ209}       | `DecisionQuotient.Sigma2PHardness.representationGap_eq_waste_plus_missing`                             |
| [DQ209]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ210}       | `DecisionQuotient.Sigma2PHardness.representationGap_missing_eq_gapCard`                                |
| [DQ210]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ211}       | `DecisionQuotient.Sigma2PHardness.representationGap_zero_iff_exactlyIdentifiesRelevant`                |
| [DQ211]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ212}       | `DecisionQuotient.Sigma2PHardness.representationGap_zero_iff_minimalSufficient`                        |
| [DQ212]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ213}       | `DecisionQuotient.Sigma2PHardness.representationGap_zero_iff_sufficient_and_subset_relevantFinset`     |
| [DQ213]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ214}       | `DecisionQuotient.Sigma2PHardness.representationGap_zero_implies_sufficient`                           |
| [DQ214]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ215}       | `DecisionQuotient.Sigma2PHardness.sufficient_iff_relevantFinset_subset`                                |
| [DQ215]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ216}       | `DecisionQuotient.Sigma2PHardness.sufficient_iff_relevant_subset`                                      |
| [DQ216]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ217}       | `DecisionQuotient.Sigma2PHardness.sufficient_of_contains_relevant`                                     |
| [DQ217]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ218}       | `DecisionQuotient.Sigma2PHardness.two_mul_add_one_lt_two_mul`                                          |
| [DQ218]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ219}       | `DecisionQuotient.Sigma2PHardness.univ_sufficient_bool`                                                |
| [DQ219]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ220}       | `DecisionQuotient.Sigma2PHardness.validI`                                                              |
| [DQ220]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ221}       | `DecisionQuotient.Sigma2PHardness.validI_I_of_x`                                                       |
| [DQ221]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ222}       | `DecisionQuotient.Sigma2PHardness.validI_iff_exists_x`                                                 |
| [DQ222]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ223}       | `DecisionQuotient.Sigma2PHardness.vector1_obstruction`                                                 |
| [DQ223]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ224}       | `DecisionQuotient.Sigma2PHardness.x00`                                                                 |
| [DQ224]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ225}       | `DecisionQuotient.Sigma2PHardness.x01`                                                                 |
| [DQ225]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ226}       | `DecisionQuotient.Sigma2PHardness.x11`                                                                 |
| [DQ226]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ227}       | `DecisionQuotient.Sigma2PHardness.yCoord`                                                              |
| [DQ227]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ228}       | `DecisionQuotient.Sigma2PHardness.yCoord_val`                                                          |
| [DQ228]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ229}       | `DecisionQuotient.Signal`                                                                              |
| [DQ229]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ230}       | `DecisionQuotient.StateAbstraction`                                                                    |
| [DQ230]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ231}       | `DecisionQuotient.StateBatchQuery`                                                                     |
| [DQ231]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ232}       | `DecisionQuotient.StructuredUtility`                                                                   |
| [DQ232]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ233}       | `DecisionQuotient.SufficiencyCheckInstance`                                                            |
| [DQ233]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ234}       | `DecisionQuotient.SufficiencyInstance`                                                                 |
| [DQ234]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ235}       | `DecisionQuotient.Summary.bounded_actions_tractable`                                                   |
| [DQ235]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ236}       | `DecisionQuotient.Summary.complexity_dichotomy`                                                        |
| [DQ236]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ237}       | `DecisionQuotient.Summary.conp_completeness`                                                           |
| [DQ237]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ238}       | `DecisionQuotient.Summary.eth_lower_bound`                                                             |
| [DQ238]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ239}       | `DecisionQuotient.Summary.min_sufficient_inapproximability`                                            |
| [DQ239]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ240}       | `DecisionQuotient.Summary.parameterized_results`                                                       |
| [DQ240]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ241}       | `DecisionQuotient.Summary.separable_utility_tractable`                                                 |
| [DQ241]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ242}       | `DecisionQuotient.Summary.sharp_p_hardness`                                                            |
| [DQ242]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ243}       | `DecisionQuotient.Summary.tractability_tightness`                                                      |
| [DQ243]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ244}       | `DecisionQuotient.Summary.tree_structure_tractable`                                                    |
| [DQ244]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ245}       | `DecisionQuotient.ThermodynamicLift.ThermoModel`                                                       |
| [DQ245]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ246}       | `DecisionQuotient.ThermodynamicLift.carbonLowerBound`                                                  |
| [DQ246]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ247}       | `DecisionQuotient.ThermodynamicLift.carbon_lower_additive`                                             |
| [DQ247]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ248}       | `DecisionQuotient.ThermodynamicLift.carbon_lower_from_bits_lower`                                      |
| [DQ248]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ249}       | `DecisionQuotient.ThermodynamicLift.carbon_lower_mandatory`                                            |
| [DQ249]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ250}       | `DecisionQuotient.ThermodynamicLift.energyLowerBound`                                                  |
| [DQ250]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ251}       | `DecisionQuotient.ThermodynamicLift.energy_lower_additive`                                             |
| [DQ251]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ252}       | `DecisionQuotient.ThermodynamicLift.energy_lower_from_bits_lower`                                      |
| [DQ252]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ253}       | `DecisionQuotient.ThermodynamicLift.energy_lower_mandatory`                                            |
| [DQ253]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ254}       | `DecisionQuotient.ThermodynamicLift.eventual_thermo_lift`                                              |
| [DQ254]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ255}       | `DecisionQuotient.ThermodynamicLift.hardness_thermo_bundle_conditional`                                |
| [DQ255]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ256}       | `DecisionQuotient.ThermodynamicLift.mandatory_conserved_bundle_conditional`                            |
| [DQ256]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ257}       | `DecisionQuotient.ThermodynamicLift.mandatory_cost_bundle`                                             |
| [DQ257]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ258}       | `DecisionQuotient.TreeStructured`                                                                      |
| [DQ258]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ259}       | `DecisionQuotient.UniverseDynamics`                                                                    |
| [DQ259]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ260}       | `DecisionQuotient.ValueQueryState`                                                                     |
| [DQ260]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ261}       | `DecisionQuotient.actions_card`                                                                        |
| [DQ261]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ262}       | `DecisionQuotient.adversarialOpt`                                                                      |
| [DQ262]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ263}       | `DecisionQuotient.adversarialOpt_eq_false_of_ne`                                                       |
| [DQ263]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ264}       | `DecisionQuotient.adversarialOpt_eq_true_of_eq`                                                        |
| [DQ264]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ265}       | `DecisionQuotient.agreeOn`                                                                             |
| [DQ265]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ266}       | `DecisionQuotient.agreeOn_flipAt`                                                                      |
| [DQ266]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ267}       | `DecisionQuotient.agreeOn_iff_subset_agreementSet`                                                     |
| [DQ267]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ268}       | `DecisionQuotient.agreeOn_xCoords_iff`                                                                 |
| [DQ268]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ269}       | `DecisionQuotient.agreementSet`                                                                        |
| [DQ269]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ270}       | `DecisionQuotient.all_coords_relevant_of_not_tautology`                                                |
| [DQ270]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ271}       | `DecisionQuotient.anchor_sufficiency_sigma2p`                                                          |
| [DQ271]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ272}       | `DecisionQuotient.anchor_sufficiency_sigma2p_nonempty`                                                 |
| [DQ272]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ273}       | `DecisionQuotient.anchoredSlice`                                                                       |
| [DQ273]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ274}       | `DecisionQuotient.anchoredSliceEquivOutside`                                                           |
| [DQ274]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ275}       | `DecisionQuotient.anchoredSlice_mul_fixed_eq_full`                                                     |
| [DQ275]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ276}       | `DecisionQuotient.approxWithin`                                                                        |
| [DQ276]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ277}       | `DecisionQuotient.bestExpectedUtility`                                                                 |
| [DQ277]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ278}       | `DecisionQuotient.bool_minimalSufficient_unique`                                                       |
| [DQ278]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ279}       | `DecisionQuotient.bool_sufficient_erase_irrelevant`                                                    |
| [DQ279]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ280}       | `DecisionQuotient.bounded_actions_complexity`                                                          |
| [DQ280]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ281}       | `DecisionQuotient.bounded_actions_polynomial_time`                                                     |
| [DQ281]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ282}       | `DecisionQuotient.buildDQProblem`                                                                      |
| [DQ282]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ283}       | `DecisionQuotient.card_anchoredSlice`                                                                  |
| [DQ283]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ284}       | `DecisionQuotient.card_anchoredSlice_eq_uniform`                                                       |
| [DQ284]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ285}       | `DecisionQuotient.card_binary_state`                                                                   |
| [DQ285]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ286}       | `DecisionQuotient.card_function_space`                                                                 |
| [DQ286]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ287}       | `DecisionQuotient.card_outside_eq_sub`                                                                 |
| [DQ287]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ288}       | `DecisionQuotient.certificate_lower_bound_for_I`                                                       |
| [DQ288]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ289}       | `DecisionQuotient.certificate_lower_bound_for_I_card`                                                  |
| [DQ289]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ290}       | `DecisionQuotient.certificate_lower_bound_for_I_card_summary`                                          |
| [DQ290]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ291}       | `DecisionQuotient.certificate_lower_bound_for_I_empty`                                                 |
| [DQ291]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ292}       | `DecisionQuotient.certificate_lower_bound_for_I_empty_summary`                                         |
| [DQ292]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ293}       | `DecisionQuotient.certificate_lower_bound_for_I_summary`                                               |
| [DQ293]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ294}       | `DecisionQuotient.certificate_lower_bound_poly`                                                        |
| [DQ294]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ295}       | `DecisionQuotient.certificate_lower_bound_poly_ge`                                                     |
| [DQ295]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ296}       | `DecisionQuotient.certificate_lower_bound_poly_ge_summary`                                             |
| [DQ296]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ297}       | `DecisionQuotient.certificate_lower_bound_poly_summary`                                                |
| [DQ297]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ298}       | `DecisionQuotient.compatibleStates`                                                                    |
| [DQ298]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ299}       | `DecisionQuotient.complexity_summary`                                                                  |
| [DQ299]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ300}       | `DecisionQuotient.constTrueFinite_empty_sufficient`                                                    |
| [DQ300]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ301}       | `DecisionQuotient.constTrueProblem`                                                                    |
| [DQ301]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ302}       | `DecisionQuotient.constTrueProblemFinite`                                                              |
| [DQ302]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ303}       | `DecisionQuotient.constTrueProblemFinite_opt`                                                          |
| [DQ303]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ304}       | `DecisionQuotient.constTrueProblem_opt`                                                                |
| [DQ304]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ305}       | `DecisionQuotient.constTrue_empty_sufficient`                                                          |
| [DQ305]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ306}       | `DecisionQuotient.const_vs_scaled_opt_view_equal`                                                      |
| [DQ306]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ307}       | `DecisionQuotient.const_vs_scaled_value_entry_diff_at_true`                                            |
| [DQ307]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ308}       | `DecisionQuotient.constant_opt_no_relevant`                                                            |
| [DQ308]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ309}       | `DecisionQuotient.constant_opt_quotientSize_one`                                                       |
| [DQ309]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ310}       | `DecisionQuotient.countSatisfyingAssignments`                                                          |
| [DQ310]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ311}       | `DecisionQuotient.countedCheckPairs`                                                                   |
| [DQ311]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ312}       | `DecisionQuotient.countedCheckPairs_steps_bound`                                                       |
| [DQ312]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ313}       | `DecisionQuotient.countedCompare`                                                                      |
| [DQ313]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ314}       | `DecisionQuotient.countedOptEqual`                                                                     |
| [DQ314]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ315}       | `DecisionQuotient.covers`                                                                              |
| [DQ315]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ316}       | `DecisionQuotient.covers_iff_agreeOn`                                                                  |
| [DQ316]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ317}       | `DecisionQuotient.cube_lt_pow`                                                                         |
| [DQ317]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ318}       | `DecisionQuotient.cubic_step_bound`                                                                    |
| [DQ318]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ319}       | `DecisionQuotient.cyclic_dependencies_coNP_hard`                                                       |
| [DQ319]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ320}       | `DecisionQuotient.decisionQuotient_cases`                                                              |
| [DQ320]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ321}       | `DecisionQuotient.decision_quotient_FPTAS`                                                             |
| [DQ321]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ322}       | `DecisionQuotient.decision_quotient_sharp_P_hard`                                                      |
| [DQ322]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ323}       | `DecisionQuotient.decode_error_sum_two_labels`                                                         |
| [DQ323]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ324}       | `DecisionQuotient.dichotomy_by_relevant_size`                                                          |
| [DQ324]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ325}       | `DecisionQuotient.distinguish_requires_target`                                                         |
| [DQ325]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ326}       | `DecisionQuotient.dqExact`                                                                             |
| [DQ326]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ327}       | `DecisionQuotient.dqProjection`                                                                        |
| [DQ327]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ328}       | `DecisionQuotient.dq_approximation_hard`                                                               |
| [DQ328]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ329}       | `DecisionQuotient.emptySufficiency_query_indistinguishable_pair`                                       |
| [DQ329]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ330}       | `DecisionQuotient.emptySufficiency_query_indistinguishable_pair_finite`                                |
| [DQ330]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ331}       | `DecisionQuotient.emptySufficiency_stateBatch_indistinguishable_pair`                                  |
| [DQ331]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ332}       | `DecisionQuotient.emptySufficiency_valueEntry_indistinguishable_pair`                                  |
| [DQ332]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ333}       | `DecisionQuotient.empty_minimal_sufficient_iff_constant`                                               |
| [DQ333]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ334}       | `DecisionQuotient.endpoints`                                                                           |
| [DQ334]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ335}       | `DecisionQuotient.endpoints_card_le`                                                                   |
| [DQ335]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ336}       | `DecisionQuotient.eth_implies_sat3_exponential`                                                        |
| [DQ336]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ337}       | `DecisionQuotient.eth_lower_bound_informal`                                                            |
| [DQ337]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ338}       | `DecisionQuotient.eth_lower_bound_sufficiency_check`                                                   |
| [DQ338]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ339}       | `DecisionQuotient.exactDQ`                                                                             |
| [DQ339]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ340}       | `DecisionQuotient.exists_coord_not_mem`                                                                |
| [DQ340]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ341}       | `DecisionQuotient.exists_distinct_patterns`                                                            |
| [DQ341]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ342}       | `DecisionQuotient.exists_forall_iff_anchor_sufficient`                                                 |
| [DQ342]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ343}       | `DecisionQuotient.exists_forall_iff_anchor_sufficient_padded`                                          |
| [DQ343]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ344}       | `DecisionQuotient.exists_not_mem_of_card_lt_univ`                                                      |
| [DQ344]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ345}       | `DecisionQuotient.exists_state_not_in_endpoints`                                                       |
| [DQ345]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ346}       | `DecisionQuotient.expectedUtility`                                                                     |
| [DQ346]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ347}       | `DecisionQuotient.exponential_query_complexity`                                                        |
| [DQ347]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ348}       | `DecisionQuotient.feasibleActions`                                                                     |
| [DQ348]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ349}       | `DecisionQuotient.flipAt`                                                                              |
| [DQ349]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ350}       | `DecisionQuotient.flipAt_ne`                                                                           |
| [DQ350]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ351}       | `DecisionQuotient.fptRunningTime`                                                                      |
| [DQ351]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ352}       | `DecisionQuotient.fpt_kernel_bound`                                                                    |
| [DQ352]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ353}       | `DecisionQuotient.full_query_distinguishes_const_spike_finite`                                         |
| [DQ353]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ354}       | `DecisionQuotient.greedy_approximation_ratio`                                                          |
| [DQ354]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ355}       | `DecisionQuotient.hard_when_all_relevant`                                                              |
| [DQ355]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ356}       | `DecisionQuotient.indistinguishable_pair_forces_one_error`                                             |
| [DQ356]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ357}       | `DecisionQuotient.indistinguishable_pair_forces_one_error_per_seed`                                    |
| [DQ357]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ358}       | `DecisionQuotient.infeasible_not_optimal_of_gap`                                                       |
| [DQ358]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ359}       | `DecisionQuotient.lawDecisionProblem`                                                                  |
| [DQ359]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ360}       | `DecisionQuotient.lawUtility`                                                                          |
| [DQ360]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ361}       | `DecisionQuotient.lawUtility_eq_of_allowed_iff`                                                        |
| [DQ361]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ362}       | `DecisionQuotient.logicallyDeterministic`                                                              |
| [DQ362]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ363}       | `DecisionQuotient.mem_compatibleStates_iff`                                                            |
| [DQ363]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ364}       | `DecisionQuotient.mem_optFinset_iff`                                                                   |
| [DQ364]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ365}       | `DecisionQuotient.mem_optimalActions_iff_actionValue`                                                  |
| [DQ365]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ366}       | `DecisionQuotient.mem_xCoords`                                                                         |
| [DQ366]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ367}       | `DecisionQuotient.min_sufficient_W2_hard`                                                              |
| [DQ367]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ368}       | `DecisionQuotient.min_sufficient_inapproximability_informal`                                           |
| [DQ368]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ369}       | `DecisionQuotient.min_sufficient_set_coNP_hard`                                                        |
| [DQ369]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ370}       | `DecisionQuotient.min_sufficient_set_inapprox_statement`                                               |
| [DQ370]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ371}       | `DecisionQuotient.mkState`                                                                             |
| [DQ371]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ372}       | `DecisionQuotient.mkState_castAdd`                                                                     |
| [DQ372]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ373}       | `DecisionQuotient.mkState_natAdd`                                                                      |
| [DQ373]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ374}       | `DecisionQuotient.monotone_opt_at_top`                                                                 |
| [DQ374]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ375}       | `DecisionQuotient.mss_equiv_relevant_card`                                                             |
| [DQ375]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ376}       | `DecisionQuotient.no_satisfying_of_count_zero`                                                         |
| [DQ376]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ377}       | `DecisionQuotient.not_tautology_iff_exists_opt_difference`                                             |
| [DQ377]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ378}       | `DecisionQuotient.numPatterns`                                                                         |
| [DQ378]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ379}       | `DecisionQuotient.optComparisonCost`                                                                   |
| [DQ379]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ380}       | `DecisionQuotient.optFinset`                                                                           |
| [DQ380]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ381}       | `DecisionQuotient.optFinset_subset_projectedOptCover`                                                  |
| [DQ381]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ382}       | `DecisionQuotient.opt_both`                                                                            |
| [DQ382]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ383}       | `DecisionQuotient.opt_falsifying`                                                                      |
| [DQ383]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ384}       | `DecisionQuotient.opt_falsifying_many`                                                                 |
| [DQ384]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ385}       | `DecisionQuotient.opt_no_only`                                                                         |
| [DQ385]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ386}       | `DecisionQuotient.opt_reference`                                                                       |
| [DQ386]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ387}       | `DecisionQuotient.opt_reference_many`                                                                  |
| [DQ387]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ388}       | `DecisionQuotient.opt_satisfying`                                                                      |
| [DQ388]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ389}       | `DecisionQuotient.opt_tautology_many`                                                                  |
| [DQ389]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ390}       | `DecisionQuotient.opt_yes_only`                                                                        |
| [DQ390]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ391}       | `DecisionQuotient.optimalActions_eq_of_separable`                                                      |
| [DQ391]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ392}       | `DecisionQuotient.optimalActions_sat`                                                                  |
| [DQ392]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ393}       | `DecisionQuotient.optimalActions_unsat`                                                                |
| [DQ393]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ394}       | `DecisionQuotient.oracleView`                                                                          |
| [DQ394]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ395}       | `DecisionQuotient.oracleViewFinite`                                                                    |
| [DQ395]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ396}       | `DecisionQuotient.oracleViewFinite_eq_of_agree`                                                        |
| [DQ396]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ397}       | `DecisionQuotient.oracleView_eq_of_agree`                                                              |
| [DQ397]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ398}       | `DecisionQuotient.over_modeling_justified`                                                             |
| [DQ398]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ399}       | `DecisionQuotient.pairCheckCost`                                                                       |
| [DQ399]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ400}       | `DecisionQuotient.parameterized_complexity_summary`                                                    |
| [DQ400]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ401}       | `DecisionQuotient.patternClass`                                                                        |
| [DQ401]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ402}       | `DecisionQuotient.poly_compose_bound`                                                                  |
| [DQ402]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ403}       | `DecisionQuotient.poly_inner_bound`                                                                    |
| [DQ403]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ404}       | `DecisionQuotient.poly_reduction_implies_many_one_exists`                                              |
| [DQ404]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ405}       | `DecisionQuotient.poly_reduction_preserves_P`                                                          |
| [DQ405]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ406}       | `DecisionQuotient.polytime_elicitation_exists_structured`                                              |
| [DQ406]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ407}       | `DecisionQuotient.proj_binary_state`                                                                   |
| [DQ407]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ408}       | `DecisionQuotient.projectToCoords`                                                                     |
| [DQ408]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ409}       | `DecisionQuotient.projectedOptCover`                                                                   |
| [DQ409]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ410}       | `DecisionQuotient.projectedOptCover_eq_opt_of_sufficient`                                              |
| [DQ410]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ411}       | `DecisionQuotient.qbfEval`                                                                             |
| [DQ411]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ412}       | `DecisionQuotient.qbfEval_mkState`                                                                     |
| [DQ412]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ413}       | `DecisionQuotient.qbfProblem`                                                                          |
| [DQ413]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ414}       | `DecisionQuotient.qbfUtility`                                                                          |
| [DQ414]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ415}       | `DecisionQuotient.queryComplexityLowerBound`                                                           |
| [DQ415]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ416}       | `DecisionQuotient.queryDistinguishes`                                                                  |
| [DQ416]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ417}       | `DecisionQuotient.query_lower_bound_statement`                                                         |
| [DQ417]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ418}       | `DecisionQuotient.quotientSize_bool_le_pow`                                                            |
| [DQ418]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ419}       | `DecisionQuotient.quotientSize_le_card`                                                                |
| [DQ419]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ420}       | `DecisionQuotient.quotientSize_le_pow_coords`                                                          |
| [DQ420]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ421}       | `DecisionQuotient.quotientSize_one_all_sufficient`                                                     |
| [DQ421]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ422}       | `DecisionQuotient.quotientSize_one_iff_constant`                                                       |
| [DQ422]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ423}       | `DecisionQuotient.quotientSize_pos`                                                                    |
| [DQ423]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ424}       | `DecisionQuotient.recoverCount`                                                                        |
| [DQ424]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ425}       | `DecisionQuotient.recoverCount_correct`                                                                |
| [DQ425]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ426}       | `DecisionQuotient.reductionProblem`                                                                    |
| [DQ426]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ427}       | `DecisionQuotient.reductionProblemMany`                                                                |
| [DQ427]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ428}       | `DecisionQuotient.reductionUtility`                                                                    |
| [DQ428]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ429}       | `DecisionQuotient.reductionUtilityMany`                                                                |
| [DQ429]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ430}       | `DecisionQuotient.reduction_not_separable`                                                             |
| [DQ430]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ431}       | `DecisionQuotient.replace_proj_other`                                                                  |
| [DQ431]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ432}       | `DecisionQuotient.replace_proj_self`                                                                   |
| [DQ432]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ433}       | `DecisionQuotient.sameProjection`                                                                      |
| [DQ433]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ434}       | `DecisionQuotient.sameProjection_trans`                                                                |
| [DQ434]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ435}       | `DecisionQuotient.sat3ToCircuit`                                                                       |
| [DQ435]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ436}       | `DecisionQuotient.sat3_reduction_size_preserving`                                                      |
| [DQ436]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ437}       | `DecisionQuotient.satSet`                                                                              |
| [DQ437]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ438}       | `DecisionQuotient.satSet_empty_of_count_zero`                                                          |
| [DQ438]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ439}       | `DecisionQuotient.scaledTrueProblem`                                                                   |
| [DQ439]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ440}       | `DecisionQuotient.scaledTrueProblem_opt`                                                               |
| [DQ440]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ441}       | `DecisionQuotient.separable_isSufficient`                                                              |
| [DQ441]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ442}       | `DecisionQuotient.sharpSAT_encoded_in_DQ`                                                              |
| [DQ442]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ443}       | `DecisionQuotient.sharpSAT_exactDQ`                                                                    |
| [DQ443]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ444}       | `DecisionQuotient.sharpSATtoDQ`                                                                        |
| [DQ444]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ445}       | `DecisionQuotient.sharpSATtoDQInstance`                                                                |
| [DQ445]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ446}       | `DecisionQuotient.single_action_always_sufficient`                                                     |
| [DQ446]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ447}       | `DecisionQuotient.someEmbedding`                                                                       |
| [DQ447]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ448}       | `DecisionQuotient.spikeFinite_empty_not_sufficient`                                                    |
| [DQ448]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ449}       | `DecisionQuotient.spikeProblem`                                                                        |
| [DQ449]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ450}       | `DecisionQuotient.spikeProblemFinite`                                                                  |
| [DQ450]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ451}       | `DecisionQuotient.spikeProblemFinite_opt_at`                                                           |
| [DQ451]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ452}       | `DecisionQuotient.spikeProblemFinite_opt_off`                                                          |
| [DQ452]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ453}       | `DecisionQuotient.spikeProblem_opt_at`                                                                 |
| [DQ453]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ454}       | `DecisionQuotient.spikeProblem_opt_off`                                                                |
| [DQ454]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ455}       | `DecisionQuotient.spike_empty_not_sufficient`                                                          |
| [DQ455]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ456}       | `DecisionQuotient.stateBatchView`                                                                      |
| [DQ456]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ457}       | `DecisionQuotient.stateBatchView_eq_if_hidden_untouched`                                               |
| [DQ457]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ458}       | `DecisionQuotient.structured_isSufficient`                                                             |
| [DQ458]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ459}       | `DecisionQuotient.succ_cube`                                                                           |
| [DQ459]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ460}       | `DecisionQuotient.sufficiencyToSetComparison`                                                          |
| [DQ460]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ461}       | `DecisionQuotient.sufficiency_FPT_coords`                                                              |
| [DQ461]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ462}       | `DecisionQuotient.sufficiency_W1_hard_unbounded_actions`                                               |
| [DQ462]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ463}       | `DecisionQuotient.sufficiency_check_coNP_hard`                                                         |
| [DQ463]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ464}       | `DecisionQuotient.sufficiency_check_polynomial`                                                        |
| [DQ464]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ465}       | `DecisionQuotient.sufficiency_iff_dq_ratio`                                                            |
| [DQ465]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ466}       | `DecisionQuotient.sufficiency_iff_projectedOptCover_eq_opt`                                            |
| [DQ466]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ467}       | `DecisionQuotient.sufficiency_in_P`                                                                    |
| [DQ467]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ468}       | `DecisionQuotient.sufficiency_poly_bounded_actions`                                                    |
| [DQ468]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ469}       | `DecisionQuotient.sufficiency_poly_separable`                                                          |
| [DQ469]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ470}       | `DecisionQuotient.sufficiency_poly_tree_structured`                                                    |
| [DQ470]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ471}       | `DecisionQuotient.sufficient_implies_tautology`                                                        |
| [DQ471]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ472}       | `DecisionQuotient.sufficient_implies_tautology_many`                                                   |
| [DQ472]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ473}       | `DecisionQuotient.sufficient_means_factorizable`                                                       |
| [DQ473]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ474}       | `DecisionQuotient.sufficient_of_projectedOptCover_eq_opt`                                              |
| [DQ474]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ475}       | `DecisionQuotient.sufficient_preserves_decisions`                                                      |
| [DQ475]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ476}       | `DecisionQuotient.targetProblem`                                                                       |
| [DQ476]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ477}       | `DecisionQuotient.targetProblem_opt_off_target`                                                        |
| [DQ477]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ478}       | `DecisionQuotient.targetProblem_opt_on_target`                                                         |
| [DQ478]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ479}       | `DecisionQuotient.targetProblems_agree_outside`                                                        |
| [DQ479]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ480}       | `DecisionQuotient.tautology_iff_opt_constant`                                                          |
| [DQ480]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ481}       | `DecisionQuotient.tautology_iff_sufficient`                                                            |
| [DQ481]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ482}       | `DecisionQuotient.tautology_iff_sufficient_many`                                                       |
| [DQ482]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ483}       | `DecisionQuotient.tautology_implies_sufficient`                                                        |
| [DQ483]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ484}       | `DecisionQuotient.tautology_implies_sufficient_many`                                                   |
| [DQ484]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ485}       | `DecisionQuotient.totalCheckCost`                                                                      |
| [DQ485]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ486}       | `DecisionQuotient.totalCheckCost_le_pow`                                                               |
| [DQ486]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ487}       | `DecisionQuotient.touchedStates`                                                                       |
| [DQ487]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ488}       | `DecisionQuotient.touchedStates_card_le_query_card`                                                    |
| [DQ488]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ489}       | `DecisionQuotient.tractability_conditions_tight`                                                       |
| [DQ489]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ490}       | `DecisionQuotient.tractable_small_state_space`                                                         |
| [DQ490]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ491}       | `DecisionQuotient.tractable_when_few_relevant`                                                         |
| [DQ491]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ492}       | `DecisionQuotient.two_actions_coNP_hard`                                                               |
| [DQ492]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ493}       | `DecisionQuotient.two_le_one_false`                                                                    |
| [DQ493]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ494}       | `DecisionQuotient.two_le_zero_false`                                                                   |
| [DQ494]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ495}       | `DecisionQuotient.two_state_sufficiency`                                                               |
| [DQ495]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ496}       | `DecisionQuotient.unique_matching_pattern`                                                             |
| [DQ496]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ497}       | `DecisionQuotient.valueEntryView`                                                                      |
| [DQ497]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ498}       | `DecisionQuotient.valueEntryView_eq_if_hidden_untouched`                                               |
| [DQ498]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ499}       | `DecisionQuotient.valueEntryView_eq_of_stateBatchView_eq_on_touched`                                   |
| [DQ499]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ500}       | `DecisionQuotient.valueOfInformation`                                                                  |
| [DQ500]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ501}       | `DecisionQuotient.valueOfInformation_const`                                                            |
| [DQ501]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ502}       | `DecisionQuotient.vectorB_blocked`                                                                     |
| [DQ502]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ503}       | `DecisionQuotient.voi_computation_sharp_P_hard`                                                        |
| [DQ503]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ504}       | `DecisionQuotient.voi_fptas_smooth_utilities`                                                          |
| [DQ504]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ505}       | `DecisionQuotient.weightedQueryCost`                                                                   |
| [DQ505]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ506}       | `DecisionQuotient.weightedQueryCost_ge_min_mul_card`                                                   |
| [DQ506]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ507}       | `DecisionQuotient.weightedQueryCost_ge_min_mul_of_card_lb`                                             |
| [DQ507]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ508}       | `DecisionQuotient.weighted_seed_error_identity`                                                        |
| [DQ508]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ509}       | `DecisionQuotient.weighted_seed_half_floor`                                                            |
| [DQ509]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ510}       | `DecisionQuotient.xCoords`                                                                             |
| [DQ510]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ511}       | `DecisionQuotient.xPart`                                                                               |
| [DQ511]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ512}       | `DecisionQuotient.xPart_mkState`                                                                       |
| [DQ512]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ513}       | `DecisionQuotient.yAllFalse`                                                                           |
| [DQ513]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ514}       | `DecisionQuotient.yAllFalse_mkState`                                                                   |
| [DQ514]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ515}       | `DecisionQuotient.yPart`                                                                               |
| [DQ515]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ516}       | `DecisionQuotient.yPart_mkState`                                                                       |
| [DQ516]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ517}       | `DecisionQuotient.Physics.Instantiation.Circuit`                                                       |
| [DQ517]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ518}       | `DecisionQuotient.Physics.Instantiation.Dynamics`                                                      |
| [DQ518]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ519}       | `DecisionQuotient.Physics.Instantiation.Geometry`                                                      |
| [DQ519]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ520}       | `DecisionQuotient.Physics.Instantiation.MoleculeCircuit`                                               |
| [DQ520]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ521}       | `DecisionQuotient.Physics.Instantiation.MoleculeDynamics`                                              |
| [DQ521]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ522}       | `DecisionQuotient.Physics.Instantiation.MoleculeGeometry`                                              |
| [DQ522]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ523}       | `DecisionQuotient.Physics.Instantiation.geometry_plus_dynamics_is_circuit`                             |
| [DQ523]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ524}       | `DecisionQuotient.Physics.Instantiation.law_objective_schema`                                          |
| [DQ524]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ525}       | `DecisionQuotient.Physics.Instantiation.law_opt_eq_feasible_of_gap`                                    |
| [DQ525]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ526}       | `DecisionQuotient.Physics.Instantiation.law_opt_singleton_of_deterministic`                            |
| [DQ526]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ527}       | `DecisionQuotient.Physics.DecisionTime.DecisionEvent`                                                  |
| [DQ527]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ528}       | `DecisionQuotient.Physics.DecisionTime.DecisionProcess`                                                |
| [DQ528]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ529}       | `DecisionQuotient.Physics.DecisionTime.SubstrateModel`                                                 |
| [DQ529]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ530}       | `DecisionQuotient.Physics.DecisionTime.TimeUnitStep`                                                   |
| [DQ530]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ531}       | `DecisionQuotient.Physics.DecisionTime.TimedState`                                                     |
| [DQ531]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ532}       | `DecisionQuotient.Physics.DecisionTime.decisionTrace`                                                  |
| [DQ532]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ533}       | `DecisionQuotient.Physics.DecisionTime.decisionTrace_length_eq_ticks`                                  |
| [DQ533]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ534}       | `DecisionQuotient.Physics.DecisionTime.decision_count_equals_elapsed_time`                             |
| [DQ534]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ535}       | `DecisionQuotient.Physics.DecisionTime.decision_event_iff_eq_tick`                                     |
| [DQ535]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ536}       | `DecisionQuotient.Physics.DecisionTime.decision_event_implies_time_unit`                               |
| [DQ536]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ537}       | `DecisionQuotient.Physics.DecisionTime.decision_taking_place_is_unit_of_time`                          |
| [DQ537]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ538}       | `DecisionQuotient.Physics.DecisionTime.run`                                                            |
| [DQ538]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ539}       | `DecisionQuotient.Physics.DecisionTime.run_elapsed_time_eq_ticks`                                      |
| [DQ539]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ540}       | `DecisionQuotient.Physics.DecisionTime.run_time_exact`                                                 |
| [DQ540]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ541}       | `DecisionQuotient.Physics.DecisionTime.substrate_step_is_time_unit`                                    |
| [DQ541]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ542}       | `DecisionQuotient.Physics.DecisionTime.substrate_step_realizes_decision_event`                         |
| [DQ542]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ543}       | `DecisionQuotient.Physics.DecisionTime.tick`                                                           |
| [DQ543]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ544}       | `DecisionQuotient.Physics.DecisionTime.tick_decision_witness`                                          |
| [DQ544]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ545}       | `DecisionQuotient.Physics.DecisionTime.tick_increments_time`                                           |
| [DQ545]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ546}       | `DecisionQuotient.Physics.DecisionTime.tick_is_decision_event`                                         |
| [DQ546]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ547}       | `DecisionQuotient.Physics.DecisionTime.time_coordinate_falsifiable`                                    |
| [DQ547]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ548}       | `DecisionQuotient.Physics.DecisionTime.time_is_discrete`                                               |
| [DQ548]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ549}       | `DecisionQuotient.Physics.DecisionTime.time_unit_law_substrate_invariant`                              |
| [DQ549]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ555}       | `DecisionQuotient.Physics.PhysicalIncompleteness.PhysicallyInstantiated`                               |
| [DQ555]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ556}       | `DecisionQuotient.Physics.PhysicalIncompleteness.UniverseModel`                                        |
| [DQ556]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ557}       | `DecisionQuotient.Physics.PhysicalIncompleteness.no_surjective_instantiation_of_card_gap`              |
| [DQ557]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ558}       | `DecisionQuotient.Physics.PhysicalIncompleteness.physical_incompleteness_of_bounds`                    |
| [DQ558]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ559}       | `DecisionQuotient.Physics.PhysicalIncompleteness.physical_incompleteness_of_card_gap`                  |
| [DQ559]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ560}       | `DecisionQuotient.HardnessDistribution.hardnessLowerBound`                                             |
| [DQ560]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ561}       | `DecisionQuotient.HardnessDistribution.hardness_is_irreducible_required_work`                          |
| [DQ561]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ562}       | `DecisionQuotient.HardnessDistribution.requiredWork`                                                   |
| [DQ562]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ563}       | `DecisionQuotient.HardnessDistribution.requiredWork_eq_affine_in_sites`                                |
| [DQ563]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ564}       | `DecisionQuotient.HardnessDistribution.workGrowthDegree`                                               |
| [DQ564]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:DQ565}       | `DecisionQuotient.HardnessDistribution.workGrowthDegree_zero_iff_eventually_constant`                  |
| [DQ565]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:F1}          | `Formula.eval`                                                                                         |
| [F1]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:F2}          | `Formula.isTautology`                                                                                  |
| [F2]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:GC1}         | `GoalClass.classMonotoneOn`                                                                            |
| [GC1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:GC2}         | `GoalClass.isNonNegativelyTautologicalCoord`                                                           |
| [GC2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:GC3}         | `GoalClass.isTautologicalCoord`                                                                        |
| [GC3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:GC4}         | `GoalClass.tautologicalSet`                                                                            |
| [GC4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD1}         | `DecisionQuotient.HardnessDistribution.centralization_dominance_bundle`                                |
| [HD1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD2}         | `DecisionQuotient.HardnessDistribution.centralization_step_saves_n_minus_one`                          |
| [HD2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD3}         | `DecisionQuotient.HardnessDistribution.centralized_higher_leverage`                                    |
| [HD3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD4}         | `DecisionQuotient.HardnessDistribution.complete_model_dominates_after_threshold`                       |
| [HD4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD5}         | `DecisionQuotient.HardnessDistribution.gap_conservation_card`                                          |
| [HD5]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD6}         | `DecisionQuotient.HardnessDistribution.generalizedTotal_with_saturation_eventually_constant`           |
| [HD6]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD7}         | `DecisionQuotient.HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`       |
| [HD7]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD8}         | `DecisionQuotient.HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`            |
| [HD8]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD9}         | `DecisionQuotient.HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower` |
| [HD9]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD10}        | `DecisionQuotient.HardnessDistribution.generalized_right_eventually_dominates_wrong`                   |
| [HD10]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD11}        | `DecisionQuotient.HardnessDistribution.hardnessEfficiency_eq_central_share`                            |
| [HD11]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD12}        | `DecisionQuotient.HardnessDistribution.isRightHardness`                                                |
| [HD12]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD13}        | `DecisionQuotient.HardnessDistribution.isWrongHardness`                                                |
| [HD13]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD14}        | `DecisionQuotient.HardnessDistribution.linear_lt_exponential_plus_constant_eventually`                 |
| [HD14]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD15}        | `DecisionQuotient.HardnessDistribution.native_dominates_manual`                                        |
| [HD15]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD16}        | `DecisionQuotient.HardnessDistribution.no_positive_slope_linear_represents_saturating`                 |
| [HD16]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD17}        | `DecisionQuotient.HardnessDistribution.right_dominates_wrong`                                          |
| [HD17]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD18}        | `DecisionQuotient.HardnessDistribution.saturatingSiteCost_eventually_constant`                         |
| [HD18]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD19}        | `DecisionQuotient.HardnessDistribution.simplicityTax_grows`                                            |
| [HD19]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD20}        | `DecisionQuotient.HardnessDistribution.totalDOF_eventually_constant_iff_zero_distributed`              |
| [HD20]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:HD21}        | `DecisionQuotient.HardnessDistribution.totalDOF_ge_intrinsic`                                          |
| [HD21]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC1}         | `DecisionQuotient.IntegrityCompetence.CertaintyInflation`                                              |
| [IC1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC2}         | `DecisionQuotient.IntegrityCompetence.CompletionFractionDefined`                                       |
| [IC2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC3}         | `DecisionQuotient.IntegrityCompetence.EvidenceForReport`                                               |
| [IC3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC4}         | `DecisionQuotient.IntegrityCompetence.ExactCertaintyInflation`                                         |
| [IC4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC5}         | `DecisionQuotient.IntegrityCompetence.Percent`                                                         |
| [IC5]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC6}         | `DecisionQuotient.IntegrityCompetence.RLFFWeights`                                                     |
| [IC6]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC7}         | `DecisionQuotient.IntegrityCompetence.ReportSignal`                                                    |
| [IC7]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC8}         | `DecisionQuotient.IntegrityCompetence.ReportBitModel`                                                  |
| [IC8]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC9}         | `DecisionQuotient.IntegrityCompetence.SignalConsistent`                                                |
| [IC9]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC10}        | `DecisionQuotient.IntegrityCompetence.admissible_irrational_strictly_more_than_rational`               |
| [IC10]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC11}        | `DecisionQuotient.IntegrityCompetence.admissible_matrix_counts`                                        |
| [IC11]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC12}        | `DecisionQuotient.IntegrityCompetence.abstain_signal_exists_with_guess_self`                           |
| [IC12]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC13}        | `DecisionQuotient.IntegrityCompetence.certaintyInflation_iff_not_admissible`                           |
| [IC13]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC14}        | `DecisionQuotient.IntegrityCompetence.certificationOverheadBits`                                       |
| [IC14]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC15}        | `DecisionQuotient.IntegrityCompetence.certificationOverheadBits_of_evidence`                           |
| [IC15]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC16}        | `DecisionQuotient.IntegrityCompetence.certificationOverheadBits_of_no_evidence`                        |
| [IC16]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC17}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits`                                              |
| [IC17]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC18}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_ge_raw`                                       |
| [IC18]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC19}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_gt_raw_of_evidence`                           |
| [IC19]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC20}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_of_evidence`                                  |
| [IC20]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC21}        | `DecisionQuotient.IntegrityCompetence.certifiedTotalBits_of_no_evidence`                               |
| [IC21]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC22}        | `DecisionQuotient.IntegrityCompetence.claim_admissible_of_evidence`                                    |
| [IC22]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC23}        | `DecisionQuotient.IntegrityCompetence.competence_implies_integrity`                                    |
| [IC23]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC24}        | `DecisionQuotient.IntegrityCompetence.completion_fraction_defined_of_declared_bound`                   |
| [IC24]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC25}        | `DecisionQuotient.IntegrityCompetence.epsilon_competence_implies_integrity`                            |
| [IC25]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC26}        | `DecisionQuotient.IntegrityCompetence.evidence_nonempty_iff_claim_admissible`                          |
| [IC26]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC27}        | `DecisionQuotient.IntegrityCompetence.evidence_of_claim_admissible`                                    |
| [IC27]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC28}        | `DecisionQuotient.IntegrityCompetence.exact_claim_admissible_iff_exact_evidence_nonempty`              |
| [IC28]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC29}        | `DecisionQuotient.IntegrityCompetence.exact_claim_requires_evidence`                                   |
| [IC29]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC30}        | `DecisionQuotient.IntegrityCompetence.exactCertaintyInflation_iff_no_exact_competence`                 |
| [IC30]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC31}        | `DecisionQuotient.IntegrityCompetence.exact_raw_only_of_no_exact_admissible`                           |
| [IC31]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC32}        | `DecisionQuotient.IntegrityCompetence.integrity_forces_abstention`                                     |
| [IC32]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC33}        | `DecisionQuotient.IntegrityCompetence.integrity_not_competent_of_nonempty_scope`                       |
| [IC33]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC34}        | `DecisionQuotient.IntegrityCompetence.integrity_resource_bound`                                        |
| [IC34]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC35}        | `DecisionQuotient.IntegrityCompetence.no_completion_fraction_without_declared_bound`                   |
| [IC35]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC36}        | `DecisionQuotient.IntegrityCompetence.overModelVerdict_rational_iff`                                   |
| [IC36]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC37}        | `DecisionQuotient.IntegrityCompetence.percentZero`                                                     |
| [IC37]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC38}        | `DecisionQuotient.IntegrityCompetence.rlffBaseReward`                                                  |
| [IC38]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC39}        | `DecisionQuotient.IntegrityCompetence.rlffReward`                                                      |
| [IC39]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC40}        | `DecisionQuotient.IntegrityCompetence.rlff_abstain_strictly_prefers_no_certificates`                   |
| [IC40]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC41}        | `DecisionQuotient.IntegrityCompetence.rlff_maximizer_has_evidence`                                     |
| [IC41]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC42}        | `DecisionQuotient.IntegrityCompetence.rlff_maximizer_is_admissible`                                    |
| [IC42]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC43}        | `DecisionQuotient.IntegrityCompetence.self_reflected_confidence_not_certification`                     |
| [IC43]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC44}        | `DecisionQuotient.IntegrityCompetence.signal_certified_positive_implies_admissible`                    |
| [IC44]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC45}        | `DecisionQuotient.IntegrityCompetence.signal_consistent_of_claim_admissible`                           |
| [IC45]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC46}        | `DecisionQuotient.IntegrityCompetence.signal_no_evidence_forces_zero_certified`                        |
| [IC46]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IC47}        | `DecisionQuotient.IntegrityCompetence.signal_exact_no_competence_forces_zero_certified`                |
| [IC47]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IPT1}        | `IsPolynomialTime.const`                                                                               |
| [IPT1]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IPT2}        | `IsPolynomialTime.of_steps_le`                                                                         |
| [IPT2]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV1}         | `DecisionQuotient.InteriorVerification.GoalClass`                                                      |
| [IV1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV2}         | `DecisionQuotient.InteriorVerification.InteriorDominanceVerifiable`                                    |
| [IV2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV3}         | `DecisionQuotient.InteriorVerification.TautologicalSetIdentifiable`                                    |
| [IV3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV4}         | `DecisionQuotient.InteriorVerification.agreeOnSet`                                                     |
| [IV4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV5}         | `DecisionQuotient.InteriorVerification.interiorParetoDominates`                                        |
| [IV5]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV6}         | `DecisionQuotient.InteriorVerification.interior_certificate_implies_non_rejection`                     |
| [IV6]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV7}         | `DecisionQuotient.InteriorVerification.interior_dominance_implies_universal_non_rejection`             |
| [IV7]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV8}         | `DecisionQuotient.InteriorVerification.interior_dominance_not_full_sufficiency`                        |
| [IV8]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IV9}         | `DecisionQuotient.InteriorVerification.interior_verification_tractable_certificate`                    |
| [IV9]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IW1}         | `InsufficiencyWitness.certifies_not_sufficient`                                                        |
| [IW1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:IW2}         | `InsufficiencyWitness.not_abstract_sufficient`                                                         |
| [IW2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L1}          | `ExactPhysicalClaimWellTyped`                                                                          |
| [L1]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L2}          | `ExcusedBy`                                                                                            |
| [L2]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L3}          | `ExplicitHardnessAssumptions`                                                                          |
| [L3]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L4}          | `Literal.eval`                                                                                         |
| [L4]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L5}          | `OneStepSequentialObjective`                                                                           |
| [L5]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L6}          | `RegimeSimulation`                                                                                     |
| [L6]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L7}          | `StandardComplexityAssumptions`                                                                        |
| [L7]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L8}          | `StochasticCriterionObjective`                                                                         |
| [L8]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L9}          | `StructureDetectable`                                                                                  |
| [L9]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L10}         | `TransitionCoupledObjective`                                                                           |
| [L10]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L11}         | `TwoStepObjective`                                                                                     |
| [L11]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L12}         | `adq`                                                                                                  |
| [L12]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L13}         | `adq_ordering`                                                                                         |
| [L13]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L14}         | `agentBridgeClass`                                                                                     |
| [L14]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L15}         | `agent_transfer_licensed_iff_snapshot`                                                                 |
| [L15]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L16}         | `anchor_sigma2p_complete_conditional`                                                                  |
| [L16]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L17}         | `anchor_sigma2p_reduction_core`                                                                        |
| [L17]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L19}         | `boundaryCharacterized_iff_exists_sufficient_subset`                                                   |
| [L19]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L20}         | `bounded_actions_detectable`                                                                           |
| [L20]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L21}         | `bounded_actions_reusable_heuristic`                                                                   |
| [L21]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L22}         | `bridgeFailureWitness`                                                                                 |
| [L22]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L23}         | `bridgeTransferLicensed`                                                                               |
| [L23]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L24}         | `bridge_boundary_represented_family`                                                                   |
| [L24]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L25}         | `boolHypercube_node_count`                                                                             |
| [L25]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L26}         | `boundaryCharacterized`                                                                                |
| [L26]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L27}         | `bridge_failure_witness_non_one_step`                                                                  |
| [L27]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L28}         | `bridge_transfer_iff_one_step_class`                                                                   |
| [L28]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L29}         | `certified_total_bits_split_core`                                                                      |
| [L29]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L30}         | `constantBoolDP`                                                                                       |
| [L30]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L31}         | `constantBoolDP_empty_sufficient`                                                                      |
| [L31]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L32}         | `constantBoolDP_opt`                                                                                   |
| [L32]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L33}         | `cost_asymmetry_eth_conditional`                                                                       |
| [L33]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L34}         | `declaredRegimeFamily`                                                                                 |
| [L34]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L35}         | `declaredRegimeFamily_complete`                                                                        |
| [L35]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L36}         | `declared_physics_no_universal_exact_certifier_core`                                                   |
| [L36]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L37}         | `dichotomy_conditional`                                                                                |
| [L37]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L38}         | `epsilon_admissible_iff_raw_lt_certified_total_core`                                                   |
| [L38]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L39}         | `exact_admissible_iff_raw_lt_certified_total_core`                                                     |
| [L39]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L40}         | `exact_certainty_inflation_under_hardness_core`                                                        |
| [L40]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L41}         | `exact_raw_eq_certified_iff_certainty_inflation_core`                                                  |
| [L41]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L42}         | `exact_raw_only_of_no_exact_admissible_core`                                                           |
| [L42]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L43}         | `explicit_assumptions_required_of_not_excused_core`                                                    |
| [L43]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L44}         | `explicit_state_upper_core`                                                                            |
| [L44]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L45}         | `firstCoordDP`                                                                                         |
| [L45]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L46}         | `firstCoordDP_empty_not_sufficient`                                                                    |
| [L46]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L47}         | `firstCoordDP_opt`                                                                                     |
| [L47]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L48}         | `hard_family_all_coords_core`                                                                          |
| [L48]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L49}         | `horizonTwoWitness`                                                                                    |
| [L49]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L50}         | `horizonTwoWitness_immediate_empty_sufficient`                                                         |
| [L50]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L51}         | `horizonTwoWitness_not_empty_sufficient_two_step`                                                      |
| [L51]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L52}         | `horizon_gt_one_bridge_can_fail_on_sufficiency`                                                        |
| [L52]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L53}         | `i0`                                                                                                   |
| [L53]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L54}         | `i0_bridge`                                                                                            |
| [L54]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L55}         | `information_barrier_opt_oracle_core`                                                                  |
| [L55]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L56}         | `information_barrier_state_batch_core`                                                                 |
| [L56]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L57}         | `information_barrier_value_entry_core`                                                                 |
| [L57]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L58}         | `integrity_resource_bound_for_sufficiency`                                                             |
| [L58]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L59}         | `integrity_universal_applicability_core`                                                               |
| [L59]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L60}         | `minsuff_collapse_core`                                                                                |
| [L60]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L61}         | `minsuff_collapse_to_conp_conditional`                                                                 |
| [L61]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L62}         | `minsuff_conp_complete_conditional`                                                                    |
| [L62]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L63}         | `no_auto_minimize_of_p_neq_conp`                                                                       |
| [L63]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L64}         | `no_exact_claim_admissible_under_hardness_core`                                                        |
| [L64]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L65}         | `no_exact_claim_under_declared_assumptions_unless_excused_core`                                        |
| [L65]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L66}         | `no_exact_identifier_implies_not_boundary_characterized`                                               |
| [L66]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L67}         | `no_uncertified_exact_claim_core`                                                                      |
| [L67]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L68}         | `node_count_does_not_determine_edge_geometry`                                                          |
| [L68]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L69}         | `one_step_bridge`                                                                                      |
| [L69]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L70}         | `oracle_lattice_transfer_as_regime_simulation`                                                         |
| [L70]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L71}         | `physical_crossover_above_cap_core`                                                                    |
| [L71]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L72}         | `physical_crossover_core`                                                                              |
| [L72]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L73}         | `physical_crossover_hardness_core`                                                                     |
| [L73]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L74}         | `physical_crossover_policy_core`                                                                       |
| [L74]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L75}         | `preferTrueSelector`                                                                                   |
| [L75]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L76}         | `process_bridge_failure_witness`                                                                       |
| [L76]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L77}         | `query_obstruction_boolean_corollary`                                                                  |
| [L77]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L78}         | `query_obstruction_finite_state_core`                                                                  |
| [L78]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L79}         | `regimeCoreClaim`                                                                                      |
| [L79]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L80}         | `regime_core_claim_proved`                                                                             |
| [L80]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L81}         | `regime_simulation_transfers_hardness`                                                                 |
| [L81]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L82}         | `reusable_heuristic_of_detectable`                                                                     |
| [L82]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L83}         | `s0_bridge`                                                                                            |
| [L83]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L84}         | `s1_bridge`                                                                                            |
| [L84]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L85}         | `sFalse`                                                                                               |
| [L85]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L86}         | `sTrue`                                                                                                |
| [L86]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L87}         | `selectorGapProblem`                                                                                   |
| [L87]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L88}         | `selectorGap_not_set_sufficient_empty`                                                                 |
| [L88]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L89}         | `selectorGap_selectorSufficient_empty`                                                                 |
| [L89]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L90}         | `selectorGap_true_mem_opt`                                                                             |
| [L90]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L91}         | `selectorSufficient_not_implies_setSufficient`                                                         |
| [L91]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L92}         | `separable_detectable`                                                                                 |
| [L92]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L93}         | `separable_reusable_heuristic`                                                                         |
| [L93]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L94}         | `snapshot_vs_process_typed_boundary`                                                                   |
| [L94]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L95}         | `standard_assumption_ledger_unpack`                                                                    |
| [L95]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L96}         | `stochasticWitness`                                                                                    |
| [L96]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L97}         | `stochastic_objective_bridge_can_fail_on_sufficiency`                                                  |
| [L97]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L98}         | `structureDetectable_of_decidable`                                                                     |
| [L98]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L99}         | `subproblem_hardness_lifts_to_full`                                                                    |
| [L99]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L100}        | `subproblem_transfer_as_regime_simulation`                                                             |
| [L100]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L101}        | `sufficiency_conp_complete_conditional`                                                                |
| [L101]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L102}        | `sufficiency_conp_reduction_core`                                                                      |
| [L102]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L103}        | `thermo_conservation_additive_core`                                                                    |
| [L103]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L104}        | `thermo_energy_carbon_lift_core`                                                                       |
| [L104]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L105}        | `thermo_eventual_lift_core`                                                                            |
| [L105]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L106}        | `thermo_hardness_bundle_core`                                                                          |
| [L106]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L107}        | `thermo_mandatory_cost_core`                                                                           |
| [L107]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L108}        | `tractable_bounded_core`                                                                               |
| [L108]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L109}        | `tractable_separable_core`                                                                             |
| [L109]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L110}        | `tractable_subcases_conditional`                                                                       |
| [L110]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L111}        | `tractable_tree_core`                                                                                  |
| [L111]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L112}        | `transitionWitness`                                                                                    |
| [L112]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L113}        | `transition_coupled_bridge_can_fail_on_sufficiency`                                                    |
| [L113]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L114}        | `tree_reusable_heuristic`                                                                              |
| [L114]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L115}        | `tree_structure_detectable`                                                                            |
| [L115]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L116}        | `typed_claim_admissibility_core`                                                                       |
| [L116]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L117}        | `typed_static_class_completeness`                                                                      |
| [L117]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:L118}        | `universal_solver_framing_core`                                                                        |
| [L118]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:OSSO1}       | `OneStepSequentialObjective.Opt`                                                                       |
| [OSSO1]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:OSSO2}       | `OneStepSequentialObjective.isSufficient`                                                              |
| [OSSO2]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:OSSO3}       | `OneStepSequentialObjective.toDecisionProblem`                                                         |
| [OSSO3]{.sans-serif}  |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PBC1}        | `DecisionQuotient.PhysicalBudgetCrossover.CrossoverAt`                                                 |
| [PBC1]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PBC2}        | `DecisionQuotient.PhysicalBudgetCrossover.explicit_infeasible_succinct_feasible_of_crossover`          |
| [PBC2]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC1}         | `PhysicalComplexity.ComputationalRequirement`                                                          |
| [PC1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC2}         | `PhysicalComplexity.InstanceSize`                                                                      |
| [PC2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC3}         | `PhysicalComplexity.Landauer_bound`                                                                    |
| [PC3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC4}         | `PhysicalComplexity.PhysicalComputer`                                                                  |
| [PC4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC5}         | `PhysicalComplexity.bit_energy_cost`                                                                   |
| [PC5]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC6}         | `PhysicalComplexity.coNP_physically_impossible`                                                        |
| [PC6]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC7}         | `PhysicalComplexity.coNP_requirement`                                                                  |
| [PC7]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC8}         | `PhysicalComplexity.k_Boltzmann`                                                                       |
| [PC8]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC9}         | `PhysicalComplexity.sufficiency_physically_impossible`                                                 |
| [PC9]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC10}        | `PhysicalComplexity.AccessRegime.AccessRegime`                                                         |
| [PC10]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC11}        | `PhysicalComplexity.AccessRegime.PhysicalDevice`                                                       |
| [PC11]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC12}        | `PhysicalComplexity.AccessRegime.RegimeEval`                                                           |
| [PC12]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC13}        | `PhysicalComplexity.AccessRegime.RegimeProof`                                                          |
| [PC13]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC14}        | `PhysicalComplexity.AccessRegime.RegimeSample`                                                         |
| [PC14]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC15}        | `PhysicalComplexity.AccessRegime.RegimeWithCertificate`                                                |
| [PC15]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC16}        | `PhysicalComplexity.AccessRegime.certificate_amortizes_hardness`                                       |
| [PC16]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC17}        | `PhysicalComplexity.AccessRegime.certificate_upgrades_regime`                                          |
| [PC17]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC18}        | `PhysicalComplexity.AccessRegime.physical_succinct_certification_hard`                                 |
| [PC18]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC19}        | `PhysicalComplexity.AccessRegime.regime_upgrade_with_certificate`                                      |
| [PC19]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC20}        | `PhysicalComplexity.AccessRegime.AccessChannelLaw`                                                     |
| [PC20]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC21}        | `PhysicalComplexity.AccessRegime.FiveWayMeet`                                                          |
| [PC21]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC22}        | `PhysicalComplexity.AccessRegime.AuditableWithCertificate`                                             |
| [PC22]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC23}        | `PhysicalComplexity.AccessRegime.HardUnderEval`                                                        |
| [PC23]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC24}        | `PhysicalComplexity.coNP_not_in_P_physically`                                                          |
| [PC24]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC25}        | `PhysicalComplexity.pow2_eventually_exceeds`                                                           |
| [PC25]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC26}        | `PhysicalComplexity.AccessRegime.RegimeEvalOn`                                                         |
| [PC26]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC27}        | `PhysicalComplexity.AccessRegime.RegimeProofOn`                                                        |
| [PC27]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC28}        | `PhysicalComplexity.AccessRegime.RegimeSampleOn`                                                       |
| [PC28]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC29}        | `PhysicalComplexity.AccessRegime.RegimeWithCertificateOn`                                              |
| [PC29]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC30}        | `PhysicalComplexity.AccessRegime.certificate_upgrades_regime_on`                                       |
| [PC30]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PC31}        | `PhysicalComplexity.AccessRegime.regime_upgrade_with_certificate_on`                                   |
| [PC31]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PD2}         | `PhysicalDevice.is_succinct`                                                                           |
| [PD2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PD3}         | `PhysicalDevice.derived_explicit_size`                                                                 |
| [PD3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PD4}         | `PhysicalDevice.is_succinct_of_gap`                                                                    |
| [PD4]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PR1}         | `PolyReduction.comp_exists`                                                                            |
| [PR1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:PR2}         | `PolyReduction.id`                                                                                     |
| [PR2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QA1}         | `QueryAlgorithm.run`                                                                                   |
| [QA1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QF1}         | `QFormula.eval`                                                                                        |
| [QF1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QF2}         | `QFormula.eval_map`                                                                                    |
| [QF2]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QF3}         | `QFormula.map`                                                                                         |
| [QF3]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:QT1}         | `QueryTranscript.size`                                                                                 |
| [QT1]{.sans-serif}    |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:S1}          | `Signal.const`                                                                                         |
| [S1]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:S2}          | `Signal.priorOn`                                                                                       |
| [S2]{.sans-serif}     |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:S2P1}        | `DecisionQuotient.Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`  |
| [S2P1]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:S2P2}        | `DecisionQuotient.Sigma2PHardness.min_representationGap_zero_iff_relevant_card`                        |
| [S2P2]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:S2P3}        | `DecisionQuotient.Sigma2PHardness.min_sufficient_set_iff_relevant_card`                                |
| [S2P3]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:S2P6}        | `DecisionQuotient.Sigma2PHardness.representationGap_eq_zero_iff`                                       |
| [S2P6]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SAT3I1}      | `SAT3Instance.inputSize`                                                                               |
| [SAT3I1]{.sans-serif} |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SCO1}        | `StochasticCriterionObjective.OptChance`                                                               |
| [SCO1]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:SCO2}        | `StochasticCriterionObjective.toExpectedDecisionProblem`                                               |
| [SCO2]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TCO1}        | `TransitionCoupledObjective.Opt`                                                                       |
| [TCO1]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TCO2}        | `TransitionCoupledObjective.score`                                                                     |
| [TCO2]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TCO3}        | `TransitionCoupledObjective.toImmediateDecisionProblem`                                                |
| [TCO3]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TSO1}        | `TwoStepObjective.Opt`                                                                                 |
| [TSO1]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TSO2}        | `TwoStepObjective.score`                                                                               |
| [TSO2]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+
| ::: {#lh:TSO3}        | `TwoStepObjective.toImmediateDecisionProblem`                                                          |
| [TSO3]{.sans-serif}   |                                                                                                        |
| :::                   |                                                                                                        |
+-----------------------+--------------------------------------------------------------------------------------------------------+


## Assumption Ledger (Auto)

#### Source files.

-   `DecisionQuotient/ClaimClosure.lean`

#### Assumption bundles and fields.

-   (No assumption bundles parsed.)

#### Conditional closure handles.

-   `DQ.anchor_sigma2p_complete_conditional`

-   `DQ.cost_asymmetry_eth_conditional`

-   `DQ.dichotomy_conditional`

-   `DQ.minsuff_collapse_to_conp_conditional`

-   `DQ.minsuff_conp_complete_conditional`

-   `DQ.sufficiency_conp_complete_conditional`

-   `DQ.tractable_subcases_conditional`


  ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  **Paper handle**                              **Status**   **Lean support**
  --------------------------------------------- ------------ -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  `cor:exact-identifiability`                   Full         `DQ.Sigma2PHardness.exactlyIdentifiesRelevant_iff_sufficient_and_subset_relevantFinset`

  `cor:exact-no-competence-zero-certified`      Full         `DQ.IntegrityCompetence.rlff_maximizer_has_evidence`

  `cor:gap-externalization`                     Full         `DQ.HardnessDistribution.saturatingSiteCost_eventually_constant`, `DQ.HardnessDistribution.totalDOF_ge_intrinsic`

  `cor:gap-minimization-hard`                   Full         `DQ.Sigma2PHardness.min_representationGap_zero_iff_relevant_card`

  `cor:generalized-eventual-dominance`          Full         `DQ.HardnessDistribution.generalized_right_dominates_wrong_of_bounded_vs_identity_lower`

  `cor:hardness-exact-certainty-inflation`      Full         `DQ.ClaimClosure.exact_certainty_inflation_under_hardness_core`

  `cor:hardness-raw-only-exact`                 Full         `DQ.ClaimClosure.exact_raw_only_of_no_exact_admissible_core`, `DQ.IntegrityCompetence.competence_implies_integrity`

  `cor:information-barrier-query`               Full         `DQ.ClaimClosure.information_barrier_opt_oracle_core`, `DQ.ClaimClosure.information_barrier_state_batch_core`, `DQ.ClaimClosure.information_barrier_value_entry_core`

  `cor:integrity-universal`                     Full         `DQ.ClaimClosure.integrity_universal_applicability_core`

  `cor:interior-singleton-certificate`          Full         `DQ.InteriorVerification.interior_verification_tractable_certificate`

  `cor:linear-positive-no-saturation`           Full         `DQ.HardnessDistribution.native_dominates_manual`

  `cor:no-auto-minimize`                        Full         `DQ.ClaimClosure.no_auto_minimize_of_p_neq_conp`

  `cor:no-uncertified-exact-claim`              Full         `DQ.ClaimClosure.no_uncertified_exact_claim_core`

  `cor:outside-excuses-no-exact-report`         Full         `DQ.ClaimClosure.no_exact_claim_under_declared_assumptions_unless_excused_core`

  `cor:overmodel-diagnostic-implication`        Full         `DQ.Sigma2PHardness.representationGap_eq_zero_iff`

  `cor:physics-no-universal-exact-claim`        Full         `DQ.ClaimClosure.no_exact_claim_admissible_under_hardness_core`

  `cor:practice-bounded`                        Full         `agent_transfer_licensed_iff_snapshot`

  `cor:practice-diagnostic`                     Full         `DQ.Sigma2PHardness.min_representationGap_zero_iff_relevant_card`

  `cor:practice-structured`                     Full         `anchor_sigma2p_complete_conditional`

  `cor:practice-tree`                           Full         `anchor_sigma2p_reduction_core`

  `cor:practice-unstructured`                   Full         `ExactPhysicalClaimWellTyped`

  `cor:query-obstruction-bool`                  Full         `DQ.ClaimClosure.query_obstruction_boolean_corollary`, `RegimeSimulation`

  `cor:right-wrong-hardness`                    Full         `DQ.HardnessDistribution.no_positive_slope_linear_represents_saturating`

  `cor:rlff-abstain-no-certs`                   Full         `DQ.IntegrityCompetence.exactCertaintyInflation_iff_no_exact_competence`

  `cor:type-system-threshold`                   Full         `DQ.HardnessDistribution.linear_lt_exponential_plus_constant_eventually`

  `prop:abstain-guess-self-signal`              Full         `DQ.IntegrityCompetence.signal_no_evidence_forces_zero_certified`

  `prop:adq-ordering`                           Full         `DQ.ClaimClosure.adq_ordering`

  `prop:attempted-competence-matrix`            Full         `DQ.IntegrityCompetence.RLFFWeights`, `DQ.IntegrityCompetence.ReportSignal`, `DQ.IntegrityCompetence.evidence_of_claim_admissible`

  `prop:bounded-slice-meta-irrelevance`         Full         `DQ.ClaimClosure.meta_coordinate_irrelevant_of_invariance_on_declared_slice`, `DQ.ClaimClosure.meta_coordinate_not_relevant_on_declared_slice`

  `prop:bridge-failure-horizon`                 Full         `DQ.ClaimClosure.horizonTwoWitness_immediate_empty_sufficient`, `DQ.ClaimClosure.horizon_gt_one_bridge_can_fail_on_sufficiency`

  `prop:bridge-failure-stochastic`              Full         `DQ.ClaimClosure.standard_assumption_ledger_unpack`

  `prop:bridge-failure-transition`              Full         `DQ.ClaimClosure.tractable_tree_core`

  `prop:bridge-transfer-scope`                  Full         `DQ.ClaimClosure.one_step_bridge`

  `prop:budgeted-crossover`                     Full         `DQ.ClaimClosure.physical_crossover_core`, `DQ.PhysicalBudgetCrossover.CrossoverAt`

  `prop:certainty-inflation-iff-inadmissible`   Full         `DQ.IntegrityCompetence.ReportBitModel`, `DQ.IntegrityCompetence.claim_admissible_of_evidence`

  `prop:certified-confidence-gate`              Full         `DQ.IntegrityCompetence.rlffBaseReward`, `DQ.IntegrityCompetence.rlffReward`

  `prop:crossover-above-cap`                    Full         `DQ.ClaimClosure.physical_crossover_above_cap_core`, `DQ.PhysicalBudgetCrossover.explicit_infeasible_succinct_feasible_of_crossover`

  `prop:crossover-not-certification`            Full         `DQ.ClaimClosure.physical_crossover_hardness_core`

  `prop:crossover-policy`                       Full         `DQ.ClaimClosure.physical_crossover_policy_core`

  `prop:decision-unit-time`                     Full         `DQ.Physics.DecisionTime.decision_event_iff_eq_tick`, `DQ.Physics.DecisionTime.decision_taking_place_is_unit_of_time`, `DQ.Physics.DecisionTime.tick_increments_time`, `DQ.Physics.DecisionTime.tick_is_decision_event`

  `prop:declared-contract-selection-validity`   Full         `DQ.ClaimClosure.explicit_assumptions_required_of_not_excused_core`, `DQ.ClaimClosure.no_exact_claim_under_declared_assumptions_unless_excused_core`, `DQ.ClaimClosure.tree_structure_detectable`

  `prop:dominance-modes`                        Full         `DQ.HardnessDistribution.centralized_higher_leverage`

  `prop:empty-sufficient-constant`              Full         `DP.anchorSufficient`

  `prop:evidence-admissibility-equivalence`     Full         `DQ.IntegrityCompetence.certifiedTotalBits`, `DQ.IntegrityCompetence.certifiedTotalBits_of_evidence`, `DQ.IntegrityCompetence.certifiedTotalBits_of_no_evidence`

  `prop:exact-requires-evidence`                Full         `DQ.IntegrityCompetence.no_completion_fraction_without_declared_bound`, `DQ.IntegrityCompetence.overModelVerdict_rational_iff`

  `prop:fraction-defined-under-bound`           Full         `DQ.IntegrityCompetence.signal_consistent_of_claim_admissible`

  `prop:generalized-assumption-boundary`        Full         `DQ.HardnessDistribution.generalizedTotal_with_saturation_eventually_constant`, `DQ.HardnessDistribution.generalized_dominance_can_fail_without_right_boundedness`

  `prop:hardness-conservation`                  Full         `DQ.HardnessDistribution.totalDOF_eventually_constant_iff_zero_distributed`

  `prop:hardness-efficiency-interpretation`     Full         `DQ.HardnessDistribution.generalized_right_eventually_dominates_wrong`

  `prop:heuristic-reusability`                  Full         `DQ.ClaimClosure.bounded_actions_detectable`, `DQ.ClaimClosure.reusable_heuristic_of_detectable`, `DQ.ClaimClosure.separable_detectable`, `DQ.ClaimClosure.transition_coupled_bridge_can_fail_on_sufficiency`

  `prop:insufficiency-counterexample`           Full         `DP.classMonotoneOn`, `DP.constant_opt_all_sufficient`

  `prop:integrity-competence-separation`        Full         `DQ.IntegrityCompetence.certifiedTotalBits_ge_raw`, `DQ.IntegrityCompetence.epsilon_competence_implies_integrity`

  `prop:integrity-resource-bound`               Full         `DQ.ClaimClosure.integrity_resource_bound_for_sufficiency`, `DQ.IntegrityCompetence.completion_fraction_defined_of_declared_bound`, `DQ.IntegrityCompetence.evidence_nonempty_iff_claim_admissible`

  `prop:interior-one-sidedness`                 Full         `DQ.InteriorVerification.interior_certificate_implies_non_rejection`, `DQ.InteriorVerification.interior_dominance_not_full_sufficiency`

  `prop:interior-universal-non-rejection`       Full         `DQ.InteriorVerification.interiorParetoDominates`

  `prop:interior-verification-tractable`        Full         `DQ.InteriorVerification.agreeOnSet`, `DQ.InteriorVerification.interior_dominance_implies_universal_non_rejection`

  `prop:minimal-relevant-equiv`                 Full         `DQ.DecisionProblem.relevantSet_is_minimal`, `DQ.DecisionProblem.sufficient_implies_selectorSufficient`

  `prop:no-evidence-zero-certified`             Full         `DQ.IntegrityCompetence.rlff_abstain_strictly_prefers_no_certificates`

  `prop:no-fraction-without-bound`              Full         `DQ.IntegrityCompetence.signal_certified_positive_implies_admissible`

  `prop:one-step-bridge`                        Full         `DQ.ClaimClosure.one_step_bridge`

  `prop:oracle-lattice-strict`                  Full         `ExplicitHardnessAssumptions`, `L.eval`

  `prop:oracle-lattice-transfer`                Full         `DQ.ClaimClosure.oracle_lattice_transfer_as_regime_simulation`, `bounded_actions_detectable`

  `prop:outside-excuses-explicit-assumptions`   Full         `DQ.ClaimClosure.explicit_assumptions_required_of_not_excused_core`

  `prop:physics-no-universal-exact`             Full         `DQ.ClaimClosure.declared_physics_no_universal_exact_certifier_core`

  `prop:query-finite-state-generalization`      Full         `StandardComplexityAssumptions`, `adq_ordering`

  `prop:query-randomized-robustness`            Full         `OneStepSequentialObjective`, `TwoStepObjective`, `adq`

  `prop:query-randomized-weighted`              Full         `bridgeTransferLicensed`, `bridge_boundary_represented_family`

  `prop:query-regime-obstruction`               Full         `DQ.ClaimClosure.query_obstruction_finite_state_core`, `StandardComplexityAssumptions`, `adq_ordering`

  `prop:query-state-batch-lb`                   Full         `StochasticCriterionObjective`, `agentBridgeClass`

  `prop:query-subproblem-transfer`              Full         `DQ.ClaimClosure.regime_simulation_transfers_hardness`, `DQ.ClaimClosure.stochastic_objective_bridge_can_fail_on_sufficiency`, `DQ.ClaimClosure.subproblem_hardness_lifts_to_full`

  `prop:query-tightness-full-scan`              Full         `TransitionCoupledObjective`

  `prop:query-value-entry-lb`                   Full         `StructureDetectable`, `boundaryCharacterized_iff_exists_sufficient_subset`

  `prop:query-weighted-transfer`                Full         `bounded_actions_reusable_heuristic`, `bridgeFailureWitness`

  `prop:raw-certified-bit-split`                Full         `DQ.ClaimClosure.certified_total_bits_split_core`, `DQ.IntegrityCompetence.admissible_irrational_strictly_more_than_rational`, `DQ.IntegrityCompetence.admissible_matrix_counts`, `DQ.IntegrityCompetence.certaintyInflation_iff_not_admissible`, `DQ.IntegrityCompetence.certificationOverheadBits`, `DQ.IntegrityCompetence.certificationOverheadBits_of_evidence`, `DQ.IntegrityCompetence.certificationOverheadBits_of_no_evidence`

  `prop:rlff-maximizer-admissible`              Full         `DQ.IntegrityCompetence.exact_raw_only_of_no_exact_admissible`, `DQ.IntegrityCompetence.integrity_forces_abstention`

  `prop:run-time-accounting`                    Full         `DQ.Physics.DecisionTime.decisionTrace_length_eq_ticks`, `DQ.Physics.DecisionTime.decision_count_equals_elapsed_time`, `DQ.Physics.DecisionTime.run_elapsed_time_eq_ticks`, `DQ.Physics.DecisionTime.run_time_exact`

  `prop:selector-separation`                    Full         `DQ.ClaimClosure.selectorSufficient_not_implies_setSufficient`

  `prop:self-confidence-not-certification`      Full         `DQ.IntegrityCompetence.signal_exact_no_competence_forces_zero_certified`

  `prop:set-to-selector`                        Full         `DQ.ClaimClosure.DecisionProblem.sufficient_iff_zeroEpsilonSufficient`

  `prop:snapshot-process-typing`                Full         `DQ.ClaimClosure.agent_transfer_licensed_iff_snapshot`, `DQ.ClaimClosure.process_bridge_failure_witness`, `DQ.ClaimClosure.snapshot_vs_process_typed_boundary`

  `prop:steps-run-scalar`                       Full         `DQ.IntegrityCompetence.rlff_maximizer_is_admissible`, `DQ.IntegrityCompetence.self_reflected_confidence_not_certification`

  `prop:substrate-unit-time`                    Full         `DQ.Physics.DecisionTime.substrate_step_is_time_unit`, `DQ.Physics.DecisionTime.substrate_step_realizes_decision_event`, `DQ.Physics.DecisionTime.time_unit_law_substrate_invariant`

  `prop:sufficiency-char`                       Full         `DQ.ClaimClosure.sufficiency_conp_reduction_core`, `DQ.ClaimClosure.sufficiency_iff_dq_ratio`

  `prop:thermo-conservation-additive`           Full         `DQ.ClaimClosure.sufficiency_iff_projectedOptCover_eq_opt`

  `prop:thermo-hardness-bundle`                 Full         `DQ.ClaimClosure.thermo_eventual_lift_core`

  `prop:thermo-lift`                            Full         `DQ.ClaimClosure.thermo_conservation_additive_core`, `DQ.ClaimClosure.thermo_energy_carbon_lift_core`

  `prop:thermo-mandatory-cost`                  Full         `DQ.ClaimClosure.thermo_hardness_bundle_core`

  `prop:time-discrete`                          Full         `DQ.Physics.DecisionTime.time_coordinate_falsifiable`, `DQ.Physics.DecisionTime.time_is_discrete`

  `prop:typed-claim-admissibility`              Full         `DQ.ClaimClosure.tree_structure_detectable`

  `prop:universal-solver-framing`               Full         `DQ.ClaimClosure.typed_static_class_completeness`

  `prop:zero-epsilon-competence`                Full         `DQ.IntegrityCompetence.certifiedTotalBits_gt_raw_of_evidence`, `DQ.IntegrityCompetence.integrity_not_competent_of_nonempty_scope`

  `prop:zero-epsilon-reduction`                 Full         `DQ.ClaimClosure.DecisionProblem.epsOpt_zero_eq_opt`, `DQ.DecisionProblem.minimalSufficient_iff_relevant`

  `thm:amortization`                            Full         `DQ.HardnessDistribution.centralized_higher_leverage`

  `thm:bridge-boundary-represented`             Full         `DQ.ClaimClosure.bridge_boundary_represented_family`, `DQ.ClaimClosure.bridge_failure_witness_non_one_step`, `DQ.ClaimClosure.bridge_transfer_iff_one_step_class`

  `thm:centralization-dominance`                Full         `DQ.HardnessDistribution.centralization_dominance_bundle`, `DQ.HardnessDistribution.centralization_step_saves_n_minus_one`

  `thm:claim-integrity-meta`                    Full         `DQ.ClaimClosure.explicit_assumptions_required_of_not_excused_core`

  `thm:config-reduction`                        Full         `DQ.ConfigReduction.config_sufficiency_iff_behavior_preserving`

  `thm:cost-asymmetry-eth`                      Full         `DQ.ClaimClosure.cost_asymmetry_eth_conditional`, `DQ.HardnessDistribution.isWrongHardness`

  `thm:dichotomy`                               Full         `DQ.ClaimClosure.dichotomy_conditional`, `DQ.ClaimClosure.explicit_state_upper_core`, `DQ.ClaimClosure.hard_family_all_coords_core`

  `thm:exact-certified-gap-iff-admissible`      Full         `DQ.ClaimClosure.epsilon_admissible_iff_raw_lt_certified_total_core`, `DQ.ClaimClosure.exact_admissible_iff_raw_lt_certified_total_core`, `DQ.ClaimClosure.exact_raw_eq_certified_iff_certainty_inflation_core`

  `thm:generalized-dominance`                   Full         `DQ.HardnessDistribution.generalized_dominance_can_fail_without_wrong_growth`

  `thm:generalized-saturation-possible`         Full         `DQ.HardnessDistribution.gap_conservation_card`, `DQ.HardnessDistribution.right_dominates_wrong`

  `thm:linear-saturation-iff-zero`              Full         `DQ.HardnessDistribution.simplicityTax_grows`

  `thm:overmodel-diagnostic`                    Full         `DQ.ClaimClosure.boundaryCharacterized_iff_exists_sufficient_subset`, `DQ.ClaimClosure.no_exact_identifier_implies_not_boundary_characterized`

  `thm:regime-coverage`                         Full         `DQ.ClaimClosure.declaredRegimeFamily_complete`, `DQ.ClaimClosure.regime_core_claim_proved`

  `thm:tax-conservation`                        Full         `DQ.HardnessDistribution.complete_model_dominates_after_threshold`

  `thm:tax-grows`                               Full         `DQ.HardnessDistribution.totalDOF_ge_intrinsic`

  `thm:tractable`                               Full         `DQ.ClaimClosure.thermo_mandatory_cost_core`, `DQ.ClaimClosure.tractable_bounded_core`, `DQ.ClaimClosure.tractable_separable_core`, `DQ.ClaimClosure.tractable_subcases_conditional`

  `thm:typed-completeness-static`               Full         `DQ.ClaimClosure.typed_claim_admissibility_core`
  ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

*Auto summary: mapped 109/109 (full=109, derived=0, unmapped=0).*




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper4_decision_quotient/proofs/`
- Lines: 11932
- Theorems: 553
- `sorry` placeholders: 0
