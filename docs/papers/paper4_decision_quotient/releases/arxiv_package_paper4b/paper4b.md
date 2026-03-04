# Paper: Decision Quotient Foundations and Convergence: Optimizer Quotients, Structural Rank, and Bayesian Optimality

**Status**: IEEE Transactions on Information Theory-ready | **Lean**: 44389 lines, 1869 theorems

---

## Abstract

_Abstract not available._

# Introduction {#sec:introduction}

The decision-relevance problem asks which parts of a state description actually matter for optimal action. This raises two natural questions: how hard relevance is to certify, and what mathematical structure emerges once the relevant-coordinate support has been identified. This paper addresses the second question.

The unifying object is the optimizer quotient. States are identified when they induce the same optimal-action set, and the resulting quotient is the coarsest abstraction that preserves the decision boundary. In **Set**, this is the familiar coimage/image factorization of the optimizer map. That quotient viewpoint immediately suggests a second question: if the quotient is the canonical lossless abstraction, what quantitative summaries of it recover the same structural content?

Our answer is that several mathematical frameworks converge on the same invariant. The support size of the relevant coordinates, which we write as $\mathrm{srank}$, reappears in quotient entropy, Fisher-style support counting, zero-distortion summaries, and the finite Bayesian chain obtained by normalizing counting measure. Convergence here means agreement across distinct mathematical lenses on the same notion of decision-relevant dimension.

The novelty does not lie in any individual ingredient. Entropy, Bayes, quotient objects, and Fisher information are all classical. The contribution is the theorem-level synthesis: once the optimizer quotient is fixed as the canonical decision-preserving abstraction, these frameworks can be compared within a single formal setting and shown to recover the same structural notion of decision-relevant dimension.

The argument is built from shared definitions, quotient structure, and information-theoretic reasoning.

## Contributions

1.  **Optimizer quotient as canonical structure.** We restate the shared foundations needed for independent readability and identify the optimizer quotient as the canonical decision-preserving abstraction.

2.  **Structural-rank recovery across frameworks.** We show that quotient entropy, Fisher-style support counting, and lossless zero-distortion summaries recover the same support-size invariant $\mathrm{srank}$.

3.  **Bayesian optimality from minimal assumptions.** We derive probability normalization, Bayes' rule, cross-entropy decomposition, and Bayes optimality under log loss from finite counting and the inequality $\log x \le x - 1$.

4.  **Machine-checked support.** The Lean development records the quotient, Bayesian, and information-theoretic lemmas used in the paper.

## Paper Structure

Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"} restates the shared foundations needed for independence. Section [\[sec:convergence-frameworks\]](#sec:convergence-frameworks){reference-type="ref" reference="sec:convergence-frameworks"} develops the quotient and structural-rank convergence story. Section [\[sec:bayesian-optimality\]](#sec:bayesian-optimality){reference-type="ref" reference="sec:bayesian-optimality"} gives the Bayesian optimality chain. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"} situates the paper relative to information theory, sufficient statistics, and formalized mathematics. Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} summarizes the corresponding Lean support.


# Formal Foundations {#sec:foundations}

This section restates the definitions needed for the paper to stand on its own. The emphasis is on sufficiency, relevance, and the quotient structure of the optimizer map.

## Decision Problems and Sufficiency

::: definition
[]{#def:decision-problem label="def:decision-problem"} A decision problem with coordinate structure is a tuple $\mathcal{D}=(A,X_1,\ldots,X_n,U)$ where $A$ is a finite action set, $S=X_1 \times \cdots \times X_n$ is the state space, and $U : A \times S \to \mathbb{Q}$ is the utility function.
:::

::: definition
[]{#def:projection label="def:projection"} For state $s=(s_1,\ldots,s_n)\in S$ and coordinate set $I \subseteq \{1,\ldots,n\}$, write $s_I$ for the projection of $s$ onto the coordinates in $I$.
:::

::: definition
[]{#def:optimizer label="def:optimizer"} The optimizer map is $$\operatorname{Opt}(s) := \arg\max_{a \in A} U(a,s).$$
:::

::: definition
[]{#def:sufficient label="def:sufficient"} Coordinate set $I$ is sufficient if $$\forall s,s' \in S:\quad s_I=s'_I \implies \operatorname{Opt}(s)=\operatorname{Opt}(s').$$
:::

::: definition
[]{#def:minimal-sufficient label="def:minimal-sufficient"} A sufficient set is minimal if no proper subset is sufficient.
:::

::: definition
[]{#def:relevant label="def:relevant"} Coordinate $i$ is relevant if there exist states that differ only at coordinate $i$ and induce different optimal-action sets: $$\exists s,s' \in S:\;
\Big(\forall j \neq i,\; s_j=s'_j\Big)
\ \wedge\
\operatorname{Opt}(s)\neq\operatorname{Opt}(s').$$
:::

::: proposition
[]{#prop:minimal-relevant-equiv label="prop:minimal-relevant-equiv"} Every minimal sufficient set is exactly the relevant-coordinate set.
:::

::: proof
*Proof.* If a coordinate in a minimal sufficient set were irrelevant, removing it would preserve sufficiency. Conversely, every sufficient set must contain every relevant coordinate because a witness to relevance is also a witness against omission. ◻
:::

::: definition
[]{#def:srank label="def:srank"} The structural rank of $\mathcal{D}$ is the cardinality of the relevant-coordinate support: $$\mathrm{srank}(\mathcal{D}) :=
\left|\{i \in \{1,\ldots,n\} : i \text{ is relevant}\}\right|.$$
:::

This quantity is the central invariant of the paper. The remaining sections ask which different mathematical summaries of a decision problem are in fact measuring this same support-size core.

## Optimizer Quotient and Coimage Structure

::: definition
[]{#def:decision-equiv label="def:decision-equiv"} States $s,s' \in S$ are decision-equivalent if $\operatorname{Opt}(s)=\operatorname{Opt}(s')$.
:::

::: definition
[]{#def:decision-quotient label="def:decision-quotient"} For coordinate set $I$ and state $s$, define $$\DQ_I(s) =
\frac{|\{a \in A : a \in \operatorname{Opt}(s') \text{ for some } s' \text{ with } s'_I=s_I\}|}{|A|}.$$
:::

::: proposition
[]{#prop:sufficiency-char label="prop:sufficiency-char"} Coordinate set $I$ is sufficient if and only if $\DQ_I(s)=|\operatorname{Opt}(s)|/|A|$ for every state $s$.
:::

::: proof
*Proof.* If $I$ is sufficient, every state in the same projection fiber has the same optimal-action set, so the numerator counts exactly the actions in $\operatorname{Opt}(s)$. Conversely, if the equality holds for all states, then no projection fiber can contain two states with different optimal-action sets. ◻
:::

::: proposition
[]{#prop:optimizer-coimage label="prop:optimizer-coimage"} The quotient of $S$ by decision equivalence is canonically equivalent to $\operatorname{range}(\operatorname{Opt})$. Equivalently, the optimizer quotient is the coimage of the optimizer map, identified with its image in **Set**.
:::

::: proof
*Proof.* Two states are identified exactly when they have the same image under $\operatorname{Opt}$, so quotient classes are in bijection with attained optimizer values. ◻
:::

::: theorem
[]{#thm:quotient-universal label="thm:quotient-universal"} Let $Q=S/{\sim}$ be the optimizer quotient, where $s \sim s'$ if and only if $\operatorname{Opt}(s)=\operatorname{Opt}(s')$, and let $\pi:S\to Q$ be the quotient map. For any surjective abstraction $\phi:S\to T$ that preserves the optimizer map in the sense that $$\phi(s)=\phi(s') \implies \operatorname{Opt}(s)=\operatorname{Opt}(s'),$$ there exists a unique map $\psi:T\to Q$ such that $\pi=\psi\circ\phi$.
:::

::: proof
*Proof.* Because $\phi$ preserves optimal-action sets, any two states in the same $\phi$-fiber are decision-equivalent. For each $t\in T$, choose $s\in S$ with $\phi(s)=t$ and define $\psi(t)=\pi(s)$. This is well-defined because different choices of $s$ in the same fiber have the same optimizer value. The identity $\pi=\psi\circ\phi$ holds by construction. Uniqueness follows because surjectivity of $\phi$ forces the value of $\psi(t)$ to be $\pi(s)$ for any preimage $s$ of $t$. ◻
:::

::: proposition
[]{#prop:optimizer-entropy-image label="prop:optimizer-entropy-image"} If $\mathrm{numOptClasses}(\mathcal{D})$ denotes the number of distinct values attained by $\operatorname{Opt}$, then $$H(\mathcal{D}) = \log_2(\mathrm{numOptClasses}(\mathcal{D}))
=
\log_2(|\operatorname{range}(\operatorname{Opt})|).$$
:::

::: proof
*Proof.* By Proposition [\[prop:optimizer-coimage\]](#prop:optimizer-coimage){reference-type="ref" reference="prop:optimizer-coimage"}, the quotient classes are exactly the points in the image of the optimizer map. ◻
:::

::: remark
[]{#rem:question-vs-problem label="rem:question-vs-problem"} The predicate "is $I$ sufficient for $\mathcal{D}$?" is encoding-independent. Complexity classes apply only after choosing how $\mathcal{D}$ and $I$ are represented. This paper uses the same shared definitions, but studies their quotient and convergence consequences rather than their class-theoretic complexity.
:::

The point of Theorem [\[thm:quotient-universal\]](#thm:quotient-universal){reference-type="ref" reference="thm:quotient-universal"} is organizational rather than terminological. In **Set**, the optimizer quotient is a familiar coimage/image construction. Its role here is to provide a common comparison object for entropy, support counting, Bayesian updating, and lossless summaries.


# Convergence Frameworks {#sec:convergence-frameworks}

This section shows that several mathematical frameworks recover the same structural invariant once the optimizer quotient has been fixed. That invariant is structural rank. The individual bridge theorems do not identify the surrounding theories with one another; they show that these theories agree on the same support-size core when exact decision preservation is the comparison criterion.

## Counting, Entropy, and the Quotient

::: theorem
[]{#thm:bayes-from-counting label="thm:bayes-from-counting"} Let $\Omega$ be a finite nonempty set and define $P(E)=|E|/|\Omega|$. Then:

1.  $P$ satisfies the finite Kolmogorov axioms;

2.  conditional probability and Bayes' rule follow algebraically wherever denominators are nonzero;

3.  mutual information is well-defined after normalization;

4.  the normalized decision-quotient score $\DQ=I(H;E)/H(H)$ lies in $[0,1]$ whenever $H(H)>0$.
:::

::: proof
*Proof.* Nonnegativity, normalization, and finite additivity are immediate from counting. Conditional probability is then defined by quotienting joint counts by marginal counts, and Bayes' rule is obtained by rearranging the identity $P(H\cap E)=P(H\mid E)P(E)=P(E\mid H)P(H)$. Mutual information and the normalized score are standard consequences once probability and entropy are defined. The bound $\DQ\in[0,1]$ follows from $0\le I(H;E)\le H(H)$. ◻
:::

::: theorem
[]{#thm:entropy-rank label="thm:entropy-rank"} For Boolean coordinate spaces, $$H(\mathcal{D}) \le \mathrm{srank}(\mathcal{D}),$$ where $H(\mathcal{D})$ is the base-$2$ entropy of the optimizer quotient.
:::

::: proof
*Proof.* The relevant-coordinate set is sufficient, so the optimizer map factors through a Boolean cube of dimension $\mathrm{srank}(\mathcal{D})$. Hence the optimizer quotient has at most $2^{\mathrm{srank}(\mathcal{D})}$ classes. ◻
:::

## Structural Rank Recovery

::: theorem
[]{#thm:fisher-rank-srank label="thm:fisher-rank-srank"} If one assigns score $1$ to relevant coordinates and $0$ to irrelevant ones, the resulting diagonal Fisher-style support matrix has rank $\mathrm{srank}(\mathcal{D})$.
:::

::: proof
*Proof.* The rank of a diagonal matrix is the number of nonzero diagonal entries, which is exactly the number of relevant coordinates. ◻
:::

::: theorem
[]{#thm:rate-distortion-bridge label="thm:rate-distortion-bridge"} At zero distortion, the minimum lossless rate needed to preserve optimal actions is governed by the same support-size quantity that defines $\mathrm{srank}(\mathcal{D})$, and any attempted compression below that support size must merge states that are not decision-equivalent.
:::

::: proof
*Proof.* Zero distortion allows only mergers of states that are already decision-equivalent. Hence the number of distinguishable summaries is controlled by the size of the optimizer quotient, which is in turn controlled by the relevant-coordinate support. ◻
:::

::: theorem
[]{#thm:nontriviality-counting label="thm:nontriviality-counting"} If a decision problem carries nonzero decision-relevant information, then its optimizer quotient is nontrivial. Equivalently, a singleton quotient cannot support positive decision-relevant entropy.
:::

::: proof
*Proof.* If the optimizer quotient has one class, then $\operatorname{Opt}$ is constant on all states. A constant optimizer map yields a single attained optimal-action set, so the quotient entropy is zero and there is no decision-relevant distinction to preserve. The contrapositive gives the result. ◻
:::

## Framework Convergence

::: theorem
[]{#thm:six-framework-recovery label="thm:six-framework-recovery"} Within the finite setting of this paper, the following objects recover the same structural core up to the identifications proved above:

1.  relevant-coordinate support,

2.  structural rank,

3.  optimizer-quotient image size,

4.  quotient entropy,

5.  Fisher-style support count,

6.  zero-distortion lossless decision summary size.
:::

::: proof
*Proof.* The equivalences are obtained by combining the foundational results of Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"}---especially Proposition [\[prop:minimal-relevant-equiv\]](#prop:minimal-relevant-equiv){reference-type="ref" reference="prop:minimal-relevant-equiv"}, Proposition [\[prop:optimizer-coimage\]](#prop:optimizer-coimage){reference-type="ref" reference="prop:optimizer-coimage"}, and Theorem [\[thm:quotient-universal\]](#thm:quotient-universal){reference-type="ref" reference="thm:quotient-universal"}---with Theorems [\[thm:entropy-rank\]](#thm:entropy-rank){reference-type="ref" reference="thm:entropy-rank"}, [\[thm:fisher-rank-srank\]](#thm:fisher-rank-srank){reference-type="ref" reference="thm:fisher-rank-srank"}, [\[thm:rate-distortion-bridge\]](#thm:rate-distortion-bridge){reference-type="ref" reference="thm:rate-distortion-bridge"}, and [\[thm:nontriviality-counting\]](#thm:nontriviality-counting){reference-type="ref" reference="thm:nontriviality-counting"}. ◻
:::

The point is not that these frameworks become identical in every technical sense. Rather, once the optimizer quotient is fixed, they converge on the same support-size invariant for decision relevance. The paper's backbone is therefore simple: shared definitions, the quotient universal property, and a family of bridge theorems centered on $\mathrm{srank}$.


# Bayesian Optimality {#sec:bayesian-optimality}

This section isolates the Bayesian chain in a stripped-down form. The key input is the inequality $\log x \le x - 1$, which yields Gibbs' inequality and therefore the standard optimality of Bayes under log loss. The substantive point is not merely that Bayes is optimal, but that the Bayes chain fits the same first-principles pattern as the quotient and entropy bridges: finite counting first, normalization second, optimization consequences third.

## Cross-Entropy Decomposition

::: theorem
[]{#thm:bayes-optimal label="thm:bayes-optimal"} For distributions $p,q$ on a finite hypothesis space, $$\mathrm{CE}(p,q)=H(p)+D_{\mathrm{KL}}(p\|q),$$ and therefore $q=p$ uniquely minimizes expected log loss.
:::

::: proof
*Proof.* Gibbs' inequality gives $D_{\mathrm{KL}}(p\|q)\ge 0$, with equality exactly when $p=q$. ◻
:::

::: theorem
[]{#thm:measure-prerequisite label="thm:measure-prerequisite"} Quantitative claims require a specified measure, while probabilistic claims require a normalized measure. Counting measure on a finite set is therefore a precursor to probability, not probability itself, until normalization is performed.
:::

::: proof
*Proof.* Expectations are integrals relative to measures. Probability is the special case in which the total mass is $1$. ◻
:::

## Decision-Quotient Ratio

::: proposition
[]{#prop:dq-range label="prop:dq-range"} The normalized decision-quotient score $$\DQ = \frac{I(H;E)}{H(H)}$$ lies in $[0,1]$ whenever $H(H)>0$.
:::

::: proof
*Proof.* Mutual information satisfies $0 \le I(H;E) \le H(H)$. ◻
:::

::: theorem
[]{#thm:bayesian-optimality-chain label="thm:bayesian-optimality-chain"} Within the finite setting of this paper, the following derivation chain holds:

1.  counting induces a finite measure;

2.  normalization turns that measure into probability;

3.  Bayes' rule follows from conditional probability;

4.  $\log x \le x-1$ yields Gibbs' inequality and KL nonnegativity;

5.  cross-entropy decomposes as entropy plus KL divergence;

6.  Bayes is therefore the unique minimizer of expected log loss.
:::

::: proof
*Proof.* The counting-to-probability part is Theorem [\[thm:bayes-from-counting\]](#thm:bayes-from-counting){reference-type="ref" reference="thm:bayes-from-counting"}. Bayes' rule is an algebraic rearrangement of the conditional-probability identity. Gibbs' inequality follows from $\log x \le x-1$, and the cross-entropy decomposition rewrites expected log loss as $H(p)+D_{\mathrm{KL}}(p\|q)$. Since KL divergence is nonnegative and vanishes only at $q=p$, Bayes uniquely minimizes expected log loss. ◻
:::

## Interpretation

The convergence claim is therefore twofold. Structurally, multiple frameworks recover $\mathrm{srank}$. Statistically, multiple inferential identities collapse to the same Bayesian optimum once the finite counting model is fixed.

The manuscript does not rely on a broad philosophical analogy between decision relevance and other frameworks. Instead it proves a sequence of concrete equivalences and bounds inside ordinary finite mathematics, with the optimizer quotient serving as the comparison object throughout.


# Related Work {#sec:related}

## Sufficient Statistics and Information Reduction

The closest classical analogue to coordinate sufficiency is the theory of sufficient statistics. In both settings the goal is to replace a large object by a smaller one without losing decision-relevant structure. The difference here is one of object and emphasis: the retained information is indexed by optimal-action preservation rather than parameter inference, and the central summary is the optimizer quotient rather than a statistic defined relative to a parametric family.

## Information Geometry and Bayesian Decision Theory

The Bayesian chain used here is standard: cross-entropy decomposes into entropy plus KL divergence, and Gibbs' inequality yields Bayes optimality under log loss. What is distinctive here is the way those classical identities are attached to the optimizer quotient and to structural rank, so that Bayesian optimality appears as one part of a larger convergence story rather than as an isolated fact.

## Rate-Distortion and Lossless Compression

The link between lossless compression and decision structure is conceptually close to the minimum-description-length viewpoint. We focus on the zero-distortion boundary relevant to exact decision preservation: once only decision-equivalent states may be merged, the quotient structure fixes the admissible compression target. This places rate-distortion language in direct contact with the relevant-coordinate support.

## Categorical and Quotient Viewpoints

The optimizer quotient is a familiar object in **Set**: it is the coimage/image factorization of the optimizer map. The contribution here is not novelty of construction but novelty of use. The quotient is the organizing object through which the Bayesian, entropy, and structural-rank viewpoints can be compared within a single framework.

## Formalized Mathematics and Verified Complexity

Formal verification has made major progress in algebra, analysis, and basic computability. The present work belongs to the growing body of research that uses mechanization to stabilize arguments spanning more than one mathematical viewpoint. Here the mechanized layer supports quotient-theoretic, information-theoretic, and Bayesian statements within a single development.


# Conclusion

This paper studies the convergence structure of decision-relevant information. Starting from shared definitions of sufficiency and relevance, it identifies the optimizer quotient as the canonical decision-preserving abstraction and shows that multiple mathematical frameworks recover the same structural core.

## What Converges {#what-converges .unnumbered}

The common invariant is structural rank: the size of the relevant-coordinate support. Quotient entropy, Fisher-style support counting, and lossless zero-distortion summaries recover that same support-size quantity once the optimizer quotient is fixed. The significance is not that these frameworks become identical, but that they agree on what counts as the dimension of decision relevance.

## Bayesian Consequence {#bayesian-consequence .unnumbered}

The Bayesian argument is equally direct. Counting on finite sets yields probability after normalization; $\log x \le x - 1$ yields Gibbs' inequality; Gibbs' inequality yields cross-entropy minimization; and Bayes emerges as the unique optimizer under log loss. This places the Bayesian conclusions on the same foundational footing as the quotient and entropy results.

## Contribution {#contribution .unnumbered}

The contribution is to place quotient structure, structural-rank recovery, and Bayesian optimality in a single mathematical framework.

## Outlook {#outlook .unnumbered}

Natural next questions are refinement questions rather than boundary questions: which additional frameworks recover the same invariant, how much of the quotient story can be internalized categorically, and which convergence statements admit the cleanest mechanized forms in Lean.


# Lean 4 Proof Listings {#app:lean}

The Lean development contains the shared definitions and the quotient-, Bayesian-, and information-theoretic lemmas used by this paper. This appendix lists the support most relevant to the main results.

## What Is Mechanized

The Lean development records:

-   core definitions of decision problems, sufficiency, relevance, and optimizer quotients,

-   quotient/image-factorization lemmas for the optimizer map,

-   finite probability and Bayesian optimality lemmas,

-   structural-rank support lemmas and related information-theoretic bridge statements.

## Lean Handle ID Map {#sec:lean-handle-id-map}

This appendix lists the handle families most relevant to the results of the paper:

-   `QT1`, `QT2`, `QT3`, `QT7` for quotient/coimage factorization;

-   `SK1`, `SK2`, `SK3` for structural-rank support facts;

-   `IT3`, `IT4` for quotient-entropy bounds;

-   `FS1`, `FS2` for Fisher-style structural-rank recovery;

-   `RS1`, `RS2`, `RS3`, `RS4`, `RD1`, `RD2`, `RD3` for rate-distortion and lossless-summary statements;

-   `BC1`--`BC5`, `FN7`, `FN8`, `FN12`, `FN14` for the finite Bayesian chain.

These are the handles most relevant to the claims developed in the manuscript. They provide a focused map from the text to the corresponding mechanized support.

## Representative Modules

-   `DecisionQuotient/Quotient.lean` -- quotient/coimage structure for the optimizer map

-   `DecisionQuotient/BayesFoundations.lean` -- finite probability and cross-entropy identities

-   `DecisionQuotient/BayesOptimalityProof.lean` -- Bayes optimality under log loss

-   `DecisionQuotient/Information.lean` and `DecisionQuotient/Information/RateDistortion.lean` -- quotient entropy and compression-facing lemmas

-   `DecisionQuotient/Statistics/FisherInformation.lean` -- support-count style structural-rank lemmas

## Scope

For readability, this appendix provides a focused manual summary rather than repository-level omnibus tables. A paper-specific handle table should include only the statements proved or cited here, together with the Lean handles that support them.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper4_decision_quotient/proofs/`
- Lines: 44389
- Theorems: 1869
- `sorry` placeholders: 0
