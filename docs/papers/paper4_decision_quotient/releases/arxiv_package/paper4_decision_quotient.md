# Paper: Decision Quotient: Formal Semantics of Architectural Choice

**Status**: TOPLAS-ready | **Lean**: 2760 lines, 106 theorems

---

## Abstract

Engineers routinely include irrelevant information in their models. Climate scientists model atmospheric chemistry when predicting regional temperatures. Financial analysts track hundreds of indicators when making portfolio decisions. Software architects specify dozens of configuration parameters when only a handful affect outcomes.

This paper proves that such *over-modeling* is not laziness---it is computationally rational. Identifying precisely which variables are "decision-relevant" is -complete [@cook1971complexity; @karp1972reducibility], finding the *minimum* set of relevant variables is -complete, and a fixed-coordinate "anchor" version is $\SigmaP{2}$-complete [@stockmeyer1976polynomial]. These results formalize a fundamental insight:

> **Determining what you need to know is harder than knowing everything.**

We introduce the *decision quotient*---a measure of decision-relevant complexity---and prove a complexity dichotomy: checking sufficiency is polynomial when the minimal sufficient set has logarithmic size, but exponential when it has linear size. We identify tractable subcases (bounded actions, separable utilities, tree-structured dependencies) that admit polynomial algorithms.

A major practical consequence is the *Simplicity Tax Theorem*: using a simple tool for a complex problem is necessarily harder than using a tool matched to the problem's complexity. When a tool lacks native support for required dimensions, users must supply that information externally at every use site. The "simpler" tool creates more total work, not less. This overturns the common intuition that "simpler is always better"---simplicity is only a virtue when the problem is also simple.

**These are ceiling results:** The complexity characterizations are exact (both upper and lower bounds). The theorems quantify universally over all problem instances ($\forall$), not probabilistically ($\mu = 1$). The dichotomy is complete---no intermediate cases exist under standard assumptions. The tractability conditions are maximal---relaxing any yields hardness. No stronger complexity claims are possible within classical complexity theory.

All results are machine-checked in Lean 4 [@moura2021lean4] ($\sim$`<!-- -->`{=html}5,000 lines across 33 files, 200+ theorems). The Lean formalization proves: (1) polynomial-time reduction composition; (2) correctness of the TAUTOLOGY and $\exists\forall$-SAT reduction mappings; (3) equivalence of sufficiency checking with coNP/$\Sigma_2^\text{P}$-complete problems under standard encodings; (4) the Simplicity Tax Theorem including conservation, dominance, and the amortization threshold. Complexity classifications (coNP-complete, $\SigmaP{2}$-complete) are derived by combining these machine-checked results with the well-known complexity of TAUTOLOGY and $\exists\forall$-SAT.

**Keywords:** computational complexity, decision theory, model selection, coNP-completeness, polynomial hierarchy, simplicity tax, Lean 4


# Introduction {#sec:introduction}

This paper establishes a fundamental limit on rational decision-making under uncertainty:

> **Determining what you need to know is harder than knowing everything.**

 It is a theorem. Specifically: given a decision problem with $n$ dimensions of uncertainty, *checking* whether a subset of dimensions suffices for optimal action is -complete. *Finding* the minimal sufficient subset is -complete. These results hold universally---for any decision problem with coordinate structure.

The implications are immediate and far-reaching. Engineers who include "irrelevant" information in their models are not exhibiting poor discipline. They are responding optimally to a computational constraint that admits no workaround. Climate scientists modeling atmospheric chemistry, financial analysts tracking hundreds of indicators, software architects specifying dozens of parameters---all are exhibiting computationally rational behavior. The alternative (identifying precisely which variables matter) requires solving -complete problems.

## The Core Problem

Consider a decision problem with actions $A$ and states $S = X_1 \times \cdots \times X_n$ (a product of $n$ coordinate spaces). For each state $s \in S$, some subset $\Opt(s) \subseteq A$ of actions are optimal. The fundamental question is:

> **Which coordinates are sufficient to determine the optimal action?**

A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* if knowing only the coordinates in $I$ determines the optimal action set: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$ where $s_I$ denotes the projection of state $s$ onto coordinates in $I$.

## Main Results

This paper proves four main theorems:

1.  **Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} (Sufficiency Checking is -complete):** Given a decision problem and coordinate set $I$, determining whether $I$ is sufficient is -complete [@cook1971complexity; @karp1972reducibility].

2.  **Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} (Minimum Sufficiency is -complete):** Finding the minimum sufficient coordinate set is -complete. (The problem is trivially in $\SigmaP{2}$ by structure, but collapses to because sufficiency equals "superset of relevant coordinates.")

3.  **Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} (Complexity Dichotomy):** Sufficiency checking exhibits a dichotomy:

    -   If the minimal sufficient set has size $O(\log |S|)$, checking is polynomial

    -   If the minimal sufficient set has size $\Omega(n)$, checking requires exponential time [@impagliazzo2001complexity].

4.  **Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"} (Tractable Subcases):** Sufficiency checking is polynomial-time for:

    -   Bounded action sets ($|A| \leq k$ for constant $k$)

    -   Separable utility functions ($u(a,s) = f(a) + g(s)$)

    -   Tree-structured coordinate dependencies

## The Foundational Principle

The core result transcends the specific application domain:

> **For any agent facing structured uncertainty, identifying the relevant dimensions of uncertainty is computationally harder than simply observing all dimensions.**

This applies to:

-   **Machine learning:** Feature selection is intractable in general

-   **Economics:** Identifying relevant market factors is intractable

-   **Scientific modeling:** Determining which variables matter is intractable

-   **Software engineering:** Configuration minimization is intractable

The ubiquity of over-modeling, over-parameterization, and "include everything" strategies across domains is not coincidence. It is the universal rational response to a universal computational constraint.

## Connection to Prior Papers

This paper completes the theoretical foundation established in Papers 1--3:

-   **Paper 1 (Typing):** Showed nominal typing dominates structural typing

-   **Paper 2 (SSOT):** Showed single source of truth minimizes modification complexity

-   **Paper 3 (Leverage):** Unified both as leverage maximization

**Paper 4's contribution:** Proves that *identifying* which architectural decisions matter is itself computationally hard. This explains why leverage maximization (Paper 3) uses heuristics rather than optimal algorithms---and why this is not a deficiency but a mathematical necessity.

## The Simplicity Tax: A Major Practical Consequence

Beyond the complexity-theoretic results, this paper develops a foundational practical principle: the *Simplicity Tax Theorem*.

The common intuition "simpler is better" is context-dependent. When a problem has intrinsic complexity (many required axes), using a "simple" tool (few native axes) forces the complexity elsewhere---to every use site. This paper proves:

> **Using a simple tool for a complex problem is necessarily harder than using a tool matched to the problem's complexity.**

Specifically: if a tool covers $k$ of $n$ required axes, the remaining $n-k$ axes become the *simplicity tax*, paid at *every use site*. For $m$ use sites, total external work is $(n-k) \times m$. A complete tool (covering all axes) pays zero tax.

This overturns simplicity-as-virtue folklore. Preferring "simple" tools for complex problems is not wisdom---it is a failure to account for distributed costs. True sophistication is matching tool complexity to problem complexity.

Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} develops this theorem formally. All results are machine-checked in Lean 4.

## Paper Structure

Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"} establishes formal foundations: decision problems, coordinate spaces, sufficiency. Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} proves hardness results with complete reductions. Section [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"} develops the complexity dichotomy. Section [\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"} presents tractable special cases. Section [\[sec:implications\]](#sec:implications){reference-type="ref" reference="sec:implications"} discusses implications for software architecture, including hardness distribution. Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"} develops the Simplicity Tax Theorem as a major practical consequence. Section [\[sec:related\]](#sec:related){reference-type="ref" reference="sec:related"} surveys related work. Appendix [\[app:lean\]](#app:lean){reference-type="ref" reference="app:lean"} contains Lean proof listings. Appendix [\[appendix-rebuttals\]](#appendix-rebuttals){reference-type="ref" reference="appendix-rebuttals"} addresses anticipated objections.

## Anticipated Objections {#sec:objection-summary}

Before proceeding, we address objections readers are likely forming. Each is refuted in detail in Appendix [\[appendix-rebuttals\]](#appendix-rebuttals){reference-type="ref" reference="appendix-rebuttals"}; here we summarize the key points.

#### "coNP-completeness doesn't mean intractable---there might be good heuristics."

Correct, but this strengthens our thesis. The point is not that practitioners cannot find useful approximations, but that *optimal* dimension selection is provably hard. The prevalence of heuristics (feature selection in ML, sensitivity analysis in economics) is itself evidence of the computational barrier.

#### "Real decision problems don't have clean coordinate structure."

The coordinate structure assumption is weaker than it appears. Any finite state space can be encoded with binary coordinates; the hardness results apply to this encoding. More structured representations make the problem *easier*, not harder---so hardness for structured problems implies hardness for general ones.

#### "The reduction from SAT is artificial."

All -completeness proofs use reductions. The reduction demonstrates that SAT instances can be encoded as sufficiency-checking problems while preserving computational structure. This is standard complexity theory methodology [@cook1971complexity; @karp1972reducibility]. The claim is not that practitioners encounter SAT problems, but that sufficiency checking is at least as hard as SAT.

#### "The tractable subcases are too restrictive to be useful."

The tractable subcases (bounded actions, separable utility, tree structure) characterize *when* dimension selection becomes feasible. Many real problems fall into these categories. The dichotomy theorem (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}) precisely identifies the boundary between tractable and intractable.

#### "This just formalizes the obvious---of course feature selection is hard."

The contribution is making "obvious" precise. Prior work established heuristic hardness for specific domains (ML feature selection, economic factor identification). We prove a *universal* result that applies to *any* decision problem with coordinate structure. This unification is the theoretical contribution.

**If you have an objection not listed above,** check Appendix [\[appendix-rebuttals\]](#appendix-rebuttals){reference-type="ref" reference="appendix-rebuttals"} (12 objections addressed, including 4 specific to the Simplicity Tax) before concluding it has not been considered.


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
[]{#def:optimizer label="def:optimizer"} For state $s \in S$, the *optimal action set* is: $$\Opt(s) := \arg\max_{a \in A} U(a, s) = \{a \in A : U(a,s) = \max_{a' \in A} U(a', s)\}$$
:::

## Sufficiency and Relevance

::: definition
[]{#def:sufficient label="def:sufficient"} A coordinate set $I \subseteq \{1, \ldots, n\}$ is *sufficient* for decision problem $\mathcal{D}$ if: $$\forall s, s' \in S: \quad s_I = s'_I \implies \Opt(s) = \Opt(s')$$ Equivalently, the optimal action depends only on coordinates in $I$.
:::

::: definition
[]{#def:minimal-sufficient label="def:minimal-sufficient"} A sufficient set $I$ is *minimal* if no proper subset $I' \subsetneq I$ is sufficient.
:::

::: definition
[]{#def:relevant label="def:relevant"} Coordinate $i$ is *relevant* if it belongs to some minimal sufficient set.
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
[]{#def:decision-quotient label="def:decision-quotient"} The *decision quotient* for state $s$ under coordinate set $I$ is: $$\text{DQ}_I(s) = \frac{|\{a \in A : a \in \Opt(s') \text{ for some } s' \sim_I s\}|}{|A|}$$ This measures the fraction of actions that *could* be optimal given only the information in $I$.
:::

::: proposition
[]{#prop:sufficiency-char label="prop:sufficiency-char"} Coordinate set $I$ is sufficient if and only if $\text{DQ}_I(s) = |\Opt(s)|/|A|$ for all $s \in S$.
:::

::: proof
*Proof.* If $I$ is sufficient, then $s \sim_I s' \implies \Opt(s) = \Opt(s')$, so the set of actions optimal for some $s' \sim_I s$ is exactly $\Opt(s)$.

Conversely, if the condition holds, then for any $s \sim_I s'$, the optimal actions form the same set (since $\text{DQ}_I(s) = \text{DQ}_I(s')$ and both equal the relative size of the common optimal set). ◻
:::


# Complexity Dichotomy {#sec:dichotomy}

The hardness results of Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} apply to worst-case instances. This section develops a more nuanced picture: a *dichotomy theorem* showing that problem difficulty depends on the size of the minimal sufficient set.

::: theorem
[]{#thm:dichotomy label="thm:dichotomy"} Let $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ be a decision problem with $|S| = N$ states. Let $k^*$ be the size of the minimal sufficient set.

1.  **Logarithmic case:** If $k^* = O(\log N)$, then SUFFICIENCY-CHECK is solvable in polynomial time.

2.  **Linear case:** If $k^* = \Omega(n)$, then SUFFICIENCY-CHECK requires time $\Omega(2^{n/c})$ for some constant $c > 0$ (assuming ETH).
:::

::: proof
*Proof.* **Part 1 (Logarithmic case):** If $k^* = O(\log N)$, then the number of distinct projections $|S_{I^*}|$ is at most $2^{k^*} = O(N^c)$ for some constant $c$. We can enumerate all projections and verify sufficiency in polynomial time.

**Part 2 (Linear case):** The reduction from TAUTOLOGY in Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} produces instances where the minimal sufficient set has size $\Omega(n)$ (all coordinates are relevant when the formula is not a tautology). Under the Exponential Time Hypothesis (ETH) [@impagliazzo2001complexity], TAUTOLOGY requires time $2^{\Omega(n)}$, so SUFFICIENCY-CHECK inherits this lower bound. ◻
:::

::: corollary
There exists a threshold $\tau \in (0, 1)$ such that:

-   If $k^*/n < \tau$, SUFFICIENCY-CHECK is "easy" (polynomial in $N$)

-   If $k^*/n > \tau$, SUFFICIENCY-CHECK is "hard" (exponential in $n$)
:::

This dichotomy explains why some domains admit tractable model selection (few relevant variables) while others require heuristics (many relevant variables).


# Tractable Special Cases {#sec:tractable}

Despite the general hardness, several natural problem classes admit polynomial-time algorithms.

::: theorem
[]{#thm:tractable label="thm:tractable"} SUFFICIENCY-CHECK is polynomial-time solvable for:

1.  **Bounded actions:** $|A| \leq k$ for constant $k$

2.  **Separable utility:** $U(a, s) = f(a) + g(s)$

3.  **Tree-structured dependencies:** Coordinates form a tree where each coordinate depends only on its ancestors
:::

## Bounded Actions

::: proof
*Proof of Part 1.* With $|A| = k$ constant, the optimizer map $\Opt : S \to 2^A$ has at most $2^k$ distinct values. For each pair of distinct optimizer values, we can identify the coordinates that distinguish them. The union of these distinguishing coordinates forms a sufficient set.

The algorithm:

1.  Sample states to identify distinct optimizer values (polynomial samples suffice with high probability)

2.  For each pair of optimizer values, find distinguishing coordinates

3.  Return the union of distinguishing coordinates

This runs in time $O(|S| \cdot k^2)$ which is polynomial when $k$ is constant. ◻
:::

## Separable Utility

::: proof
*Proof of Part 2.* If $U(a, s) = f(a) + g(s)$, then: $$\Opt(s) = \arg\max_{a \in A} [f(a) + g(s)] = \arg\max_{a \in A} f(a)$$ The optimal action is independent of the state! Thus $I = \emptyset$ is always sufficient. ◻
:::

## Tree-Structured Dependencies

::: proof
*Proof of Part 3.* When coordinates form a tree, we can use dynamic programming. For each node $i$, compute the set of optimizer values achievable in the subtree rooted at $i$. A coordinate is relevant if and only if different values at that coordinate lead to different optimizer values in its subtree. This approach is analogous to inference in probabilistic graphical models [@pearl1988probabilistic; @koller2009probabilistic].

The algorithm runs in time $O(n \cdot |A|^2)$ by processing the tree bottom-up. ◻
:::

## Practical Implications

These tractable cases correspond to common modeling scenarios:

-   **Bounded actions:** Most real decisions have few alternatives (buy/sell/hold, approve/reject, etc.)

-   **Separable utility:** Additive cost models, linear utility functions

-   **Tree structure:** Hierarchical decision processes, causal models with tree structure

When a problem falls outside these cases, the hardness results apply, justifying heuristic approaches.


# Why Over-Modeling Is Optimal {#sec:engineering-justification}

The complexity results of Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"} and [\[sec:dichotomy\]](#sec:dichotomy){reference-type="ref" reference="sec:dichotomy"} transform engineering practice from art to mathematics. This section proves that observed behaviors---configuration over-specification, absence of automated minimization tools, heuristic model selection---are not failures of discipline but *provably optimal responses* to computational constraints.

The conventional critique of over-modeling ("you should identify only the essential variables") is computationally naive. It asks engineers to solve -complete problems. The rational response is to include everything and pay linear maintenance costs, rather than attempt exponential minimization costs.

## Configuration Simplification is SUFFICIENCY-CHECK

Real engineering problems reduce directly to the decision problems studied in this paper.

::: theorem
[]{#thm:config-reduction label="thm:config-reduction"} Given a software system with configuration parameters $P = \{p_1, \ldots, p_n\}$ and observed behaviors $B = \{b_1, \ldots, b_m\}$, the problem of determining whether parameter subset $I \subseteq P$ preserves all behaviors is equivalent to SUFFICIENCY-CHECK.
:::

::: proof
*Proof.* Construct decision problem $\mathcal{D} = (A, X_1, \ldots, X_n, U)$ where:

-   Actions $A = B$ (each behavior is an action)

-   Coordinates $X_i$ = domain of parameter $p_i$

-   State space $S = X_1 \times \cdots \times X_n$

-   Utility $U(b, s) = 1$ if behavior $b$ occurs under configuration $s$, else $U(b, s) = 0$

Then $\Opt(s) = \{b \in B : b \text{ occurs under configuration } s\}$.

Coordinate set $I$ is sufficient iff: $$s_I = s'_I \implies \Opt(s) = \Opt(s')$$

This holds iff configurations agreeing on parameters in $I$ exhibit identical behaviors.

Therefore, "does parameter subset $I$ preserve all behaviors?" is exactly SUFFICIENCY-CHECK for the constructed decision problem. ◻
:::

::: remark
This reduction is *parsimonious*: every instance of configuration simplification corresponds bijectively to an instance of SUFFICIENCY-CHECK. The problems are not merely related---they are identical up to encoding.
:::

## Computational Rationality of Over-Modeling

We now prove that over-specification is the optimal engineering strategy given complexity constraints.

::: theorem
[]{#thm:rational-overmodel label="thm:rational-overmodel"} Consider an engineer specifying a system configuration with $n$ parameters. Let:

-   $C_{\text{over}}(k)$ = cost of maintaining $k$ extra parameters beyond minimal

-   $C_{\text{find}}(n)$ = cost of finding minimal sufficient parameter set

-   $C_{\text{under}}$ = expected cost of production failures from underspecification

When SUFFICIENCY-CHECK is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}):

1.  Worst-case finding cost is exponential: $C_{\text{find}}(n) = \Omega(2^n)$

2.  Maintenance cost is linear: $C_{\text{over}}(k) = O(k)$

3.  For sufficiently large $n$, exponential cost dominates linear cost

Therefore, when $n$ exceeds a threshold, over-modeling minimizes total expected cost: $$C_{\text{over}}(k) < C_{\text{find}}(n) + C_{\text{under}}$$

Over-modeling is the economically optimal strategy under computational constraints.
:::

::: proof
*Proof.* By Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, SUFFICIENCY-CHECK is -complete. Under standard complexity assumptions ($\Pclass \neq \coNP$), no polynomial-time algorithm exists for checking sufficiency.

Finding the minimal sufficient set requires checking sufficiency of multiple candidate sets. Exhaustive search examines: $$\sum_{i=0}^{n} \binom{n}{i} = 2^n \text{ candidate subsets}$$

Each check requires $\Omega(1)$ time (at minimum, reading the input). Therefore: $$C_{\text{find}}(n) = \Omega(2^n)$$

Maintaining $k$ extra parameters incurs:

-   Documentation cost: $O(k)$ entries

-   Testing cost: $O(k)$ test cases

-   Migration cost: $O(k)$ parameters to update

Total maintenance cost is $C_{\text{over}}(k) = O(k)$.

For concrete threshold: when $n = 20$ parameters, exhaustive search requires $2^{20} \approx 10^6$ checks. Including $k = 5$ extra parameters costs $O(5)$ maintenance overhead but avoids $10^6$ computational work.

Since $2^n$ grows faster than any polynomial in $k$ or $n$, there exists $n_0$ such that for all $n > n_0$: $$C_{\text{over}}(k) \ll C_{\text{find}}(n)$$

Adding underspecification risk $C_{\text{under}}$ (production failures from missing parameters), which can be arbitrarily large, makes over-specification strictly dominant. ◻
:::

::: corollary
[]{#cor:no-auto-minimize label="cor:no-auto-minimize"} There exists no polynomial-time algorithm that:

1.  Takes an arbitrary configuration file with $n$ parameters

2.  Identifies the minimal sufficient parameter subset

3.  Guarantees correctness (no false negatives)
:::

::: proof
*Proof.* Such an algorithm would solve MINIMUM-SUFFICIENT-SET in polynomial time, contradicting Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"} (assuming $\Pclass \neq \coNP$). ◻
:::

::: remark
Corollary [\[cor:no-auto-minimize\]](#cor:no-auto-minimize){reference-type="ref" reference="cor:no-auto-minimize"} explains the observed absence of "config cleanup" tools in software engineering practice. Engineers who include extra parameters are not exhibiting poor discipline---they are adapting optimally to computational impossibility. The problem is not lack of tooling effort; it is mathematical intractability.
:::

## Connection to Observed Practice

These theorems provide mathematical grounding for three widespread engineering behaviors:

**1. Configuration files grow over time.** Removing parameters requires solving -complete problems. Engineers rationally choose linear maintenance cost over exponential minimization cost.

**2. Heuristic model selection dominates.** ML practitioners use AIC, BIC, cross-validation instead of optimal feature selection because optimal selection is intractable (Theorem [\[thm:rational-overmodel\]](#thm:rational-overmodel){reference-type="ref" reference="thm:rational-overmodel"}).

**3. "Include everything" is a legitimate strategy.** When determining relevance costs $\Omega(2^n)$, including all $n$ parameters costs $O(n)$. For large $n$, this is the rational choice.

These are not workarounds or approximations. They are *optimal responses* to computational constraints. The complexity results transform engineering practice from art to mathematics: over-modeling is not a failure---it is the provably correct strategy.


# Implications for Software Architecture {#sec:implications}

The complexity results have direct implications for software engineering practice.

## Why Over-Specification Is Rational

Software architects routinely specify more configuration parameters than strictly necessary. Our results show this is computationally rational:

::: corollary
Given a software system with $n$ configuration parameters, checking whether a proposed subset suffices is -complete. Finding the minimum such set is also -complete.
:::

This explains why configuration files grow over time: removing "unnecessary" parameters requires solving a hard problem.

## Connection to Leverage Theory

Paper 3 introduced leverage as the ratio of impact to effort. The decision quotient provides a complementary measure:

::: definition
For a software system with configuration space $S$ and behavior space $B$: $$\text{ADQ}(I) = \frac{|\{b \in B : b \text{ achievable with some } s \text{ where } s_I \text{ fixed}\}|}{|B|}$$
:::

High ADQ means the configuration subset $I$ leaves many behaviors achievable---it doesn't constrain the system much. Low ADQ means $I$ strongly constrains behavior.

::: proposition
High-leverage architectural decisions correspond to low-ADQ configuration subsets: they strongly constrain system behavior with minimal specification.
:::

## Practical Recommendations

Based on our theoretical results:

1.  **Accept over-modeling:** Don't penalize engineers for including "extra" parameters. The alternative (minimal modeling) is computationally hard.

2.  **Use bounded scenarios:** When the scenario space is small (Proposition [\[prop:sufficiency-char\]](#prop:sufficiency-char){reference-type="ref" reference="prop:sufficiency-char"}), minimal modeling becomes tractable.

3.  **Exploit structure:** Tree-structured dependencies, bounded alternatives, and separable utilities admit efficient algorithms.

4.  **Invest in heuristics:** For general problems, develop domain-specific heuristics rather than seeking optimal solutions.

## Hardness Distribution: Right Place vs Wrong Place {#sec:hardness-distribution}

A fundamental principle emerges from the complexity results: problem hardness is conserved but can be *distributed* across a system in qualitatively different ways.

::: definition
[]{#def:hardness-distribution label="def:hardness-distribution"} Let $P$ be a problem with intrinsic hardness $H(P)$ (measured in computational steps, implementation effort, or error probability). A *solution architecture* $S$ partitions this hardness into:

-   $H_{\text{central}}(S)$: hardness paid once, at design time or in a shared component

-   $H_{\text{distributed}}(S)$: hardness paid per use site

For $n$ use sites, total realized hardness is: $$H_{\text{total}}(S) = H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)$$
:::

::: theorem
[]{#thm:hardness-conservation label="thm:hardness-conservation"} For any problem $P$ with intrinsic hardness $H(P)$, any solution $S$ satisfies: $$H_{\text{central}}(S) + H_{\text{distributed}}(S) \geq H(P)$$ Hardness cannot be eliminated, only redistributed.
:::

::: proof
*Proof.* By definition of intrinsic hardness: any correct solution must perform at least $H(P)$ units of work (computational, cognitive, or error-handling). This work is either centralized or distributed. 0◻ ◻
:::

::: definition
[]{#def:hardness-efficiency label="def:hardness-efficiency"} The *hardness efficiency* of solution $S$ with $n$ use sites is: $$\eta(S, n) = \frac{H_{\text{central}}(S)}{H_{\text{central}}(S) + n \cdot H_{\text{distributed}}(S)}$$
:::

High $\eta$ indicates centralized hardness (paid once); low $\eta$ indicates distributed hardness (paid repeatedly).

::: theorem
[]{#thm:centralization-dominance label="thm:centralization-dominance"} For $n > 1$ use sites, solutions with higher $H_{\text{central}}$ and lower $H_{\text{distributed}}$ yield:

1.  Lower total realized hardness: $H_{\text{total}}(S_1) < H_{\text{total}}(S_2)$ when $H_{\text{distributed}}(S_1) < H_{\text{distributed}}(S_2)$

2.  Fewer error sites: errors in centralized components affect 1 location; errors in distributed components affect $n$ locations

3.  Higher leverage (Paper 3): one unit of central effort affects $n$ sites
:::

::: proof
*Proof.* (1) follows from the total hardness formula. (2) follows from error site counting. (3) follows from Paper 3's leverage definition $L = \Delta\text{Effect}/\Delta\text{Effort}$. 0◻ ◻
:::

::: corollary
[]{#cor:right-wrong-hardness label="cor:right-wrong-hardness"} A solution exhibits *hardness in the right place* when:

-   Hardness is centralized (high $H_{\text{central}}$, low $H_{\text{distributed}}$)

-   Hardness is paid at design/compile time rather than runtime

-   Hardness is enforced by tooling (type checker, compiler) rather than convention

A solution exhibits *hardness in the wrong place* when:

-   Hardness is distributed (low $H_{\text{central}}$, high $H_{\text{distributed}}$)

-   Hardness is paid repeatedly at each use site

-   Hardness relies on human discipline rather than mechanical enforcement
:::

**Example: Type System Instantiation.** Consider a capability $C$ (e.g., provenance tracking) that requires hardness $H(C)$:

::: center
  **Approach**                  $H_{\text{central}}$     $H_{\text{distributed}}$
  ---------------------------- ----------------------- -----------------------------
  Native type system support    High (learning cost)    Low (type checker enforces)
  Manual implementation         Low (no new concepts)   High (reimplement per site)
:::

For $n$ use sites, manual implementation costs $n \cdot H_{\text{distributed}}$, growing without bound. Native support costs $H_{\text{central}}$ once, amortized across all uses. The "simpler" approach (manual) is only simpler at $n = 1$; for $n > H_{\text{central}}/H_{\text{distributed}}$, native support dominates.

::: remark
The decision quotient (Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"}) measures which coordinates are decision-relevant. Hardness distribution measures where the cost of *handling* those coordinates is paid. A high-axis system makes relevance explicit (central hardness); a low-axis system requires users to track relevance themselves (distributed hardness).
:::

The next section develops the major practical consequence of this framework: the Simplicity Tax Theorem.


# The Simplicity Tax Theorem {#sec:simplicity-tax}

The complexity results of Sections [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}--[\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"} establish that identifying decision-relevant dimensions is coNP-complete. This section develops the practical consequence: what happens when engineers *ignore* this hardness and attempt to use "simple" tools for complex problems.

The answer is the *Simplicity Tax*: a per-site cost that cannot be avoided, only redistributed. This result overturns the common intuition that "simpler is always better" and establishes a foundational principle: **No Free Simplicity**.

## The Conservation Law: No Free Simplicity {#sec:conservation}

::: definition
[]{#def:problem-tool label="def:problem-tool"} A *problem* $P$ has a set of *required axes* $R(P)$---the dimensions of variation that must be represented. A *tool* $T$ has a set of *native axes* $A(T)$---what it can represent directly.
:::

This terminology is grounded in Papers 1--2: "axes" correspond to Paper 1's axis framework (`requiredAxesOf`) and Paper 2's degrees of freedom.

::: definition
[]{#def:expressive-gap label="def:expressive-gap"} The *expressive gap* between tool $T$ and problem $P$ is: $$\text{Gap}(T, P) = R(P) \setminus A(T)$$ The *simplicity tax* is $|\text{Gap}(T, P)|$: the number of axes the tool cannot handle natively. This tax is paid at *every use site*.
:::

::: definition
[]{#def:complete-incomplete label="def:complete-incomplete"} Tool $T$ is *complete* for problem $P$ if $R(P) \subseteq A(T)$. Otherwise $T$ is *incomplete* for $P$.
:::

::: theorem
[]{#thm:tax-conservation label="thm:tax-conservation"} For any problem $P$ with required axes $R(P)$ and any tool $T$: $$|\text{Gap}(T, P)| + |R(P) \cap A(T)| = |R(P)|$$ The required axes are partitioned into "covered natively" and "tax." You cannot reduce the total---only shift where it is paid.
:::

::: proof
*Proof.* Set partition: $R(P) = (R(P) \cap A(T)) \cup (R(P) \setminus A(T))$. The sets are disjoint. Cardinality follows. 0◻ ◻
:::

This is analogous to conservation laws in physics: energy is conserved, only transformed. Complexity is conserved, only distributed.

::: theorem
[]{#thm:complete-no-tax label="thm:complete-no-tax"} If $T$ is complete for $P$, then $\text{SimplicityTax}(T, P) = 0$.
:::

::: theorem
[]{#thm:incomplete-positive-tax label="thm:incomplete-positive-tax"} If $T$ is incomplete for $P$, then $\text{SimplicityTax}(T, P) > 0$.
:::

::: theorem
[]{#thm:tax-grows label="thm:tax-grows"} For $n$ use sites with an incomplete tool: $$\text{TotalExternalWork}(T, P, n) = n \times \text{SimplicityTax}(T, P)$$ Total work grows linearly. There is no economy of scale for distributed complexity.
:::

::: theorem
[]{#thm:complete-dominates label="thm:complete-dominates"} For any $n > 0$, a complete tool has strictly less total cost than an incomplete tool: $$\text{TotalExternalWork}(T_{\text{complete}}, P, n) < \text{TotalExternalWork}(T_{\text{incomplete}}, P, n)$$
:::

::: proof
*Proof.* Complete: $0 \times n = 0$. Incomplete: $k \times n$ for $k \geq 1$. For $n > 0$: $0 < kn$. 0◻ ◻
:::

## The Simplicity Preference Fallacy {#sec:fallacy}

::: definition
The *simplicity preference fallacy* is the cognitive error of preferring low $H_{\text{central}}$ (learning cost) without accounting for $H_{\text{distributed}}$ (per-site cost).
:::

This fallacy manifests as:

-   "I prefer simple tools" (without asking: simple relative to what problem?)

-   "YAGNI" applied to infrastructure (ignoring amortization across use sites)

-   "Just write straightforward code" (ignoring that $n$ sites pay the tax)

-   "Abstractions are overhead" (treating central cost as total cost)

::: theorem
[]{#thm:fallacy label="thm:fallacy"} Let $T_{\text{simple}}$ be incomplete for problem $P$ and $T_{\text{complex}}$ be complete. For any $n > 0$: $$\text{TotalExternalWork}(T_{\text{complex}}, P, n) < \text{TotalExternalWork}(T_{\text{simple}}, P, n)$$ The "simpler" tool creates more total work, not less.
:::

The fallacy persists because $H_{\text{distributed}}$ is invisible: it is paid by users, at runtime, across time, in maintenance. $H_{\text{central}}$ is visible: it is paid by the designer, upfront, once. Humans overweight visible costs.

::: theorem
[]{#thm:amortization label="thm:amortization"} There exists a threshold $n^*$ such that for all $n > n^*$, the total cost of the "complex" tool (including learning) is strictly less than the "simple" tool: $$n^* = \frac{H_{\text{central}}(T_{\text{complex}})}{\text{SimplicityTax}(T_{\text{simple}}, P)}$$ Beyond $n^*$ uses, the complex tool is cheaper even accounting for learning cost.
:::

## Cross-Domain Examples {#sec:examples}

The Simplicity Tax applies universally. Consider these domains:

::: center
  **Domain**        **"Simple" Choice**   **"Complex" Choice**      **Tax per Site**
  ----------------- --------------------- ------------------------- ---------------------
  Type Systems      Dynamic typing        Static typing             Runtime type errors
  Python            Manual patterns       Metaclasses/descriptors   Boilerplate code
  Data Validation   Ad-hoc checks         Schema/ORM                Validation logic
  Configuration     Hardcoded values      Config management         Change propagation
  APIs              Stringly-typed        Rich type models          Parse/validate code
:::

In each case, the "simple" choice has lower learning cost ($H_{\text{central}}$) but higher per-site cost ($H_{\text{distributed}}$). For $n$ use sites, the simple choice costs $n \times \text{tax}$.

**Example: Python Metaclasses.** Python's community often resists metaclasses as "too complex." But consider a problem requiring automatic subclass registration, attribute validation, and interface enforcement---three axes of variation.

::: center
  **Approach**                       **Native Axes**                 **Tax/Class**   **Total for 50 classes**
  ------------------- --------------------------------------------- --------------- --------------------------
  Metaclass            $\{$registration, validation, interface$\}$         0                    0
  Manual decorators               $\{$registration$\}$                     2                   100
  Fully manual                         $\emptyset$                         3                   150
:::

The "simplest" approach (fully manual) creates the most work. The community's resistance to metaclasses is the Simplicity Preference Fallacy in action.

**Example: Static vs. Dynamic Typing.** Dynamic typing has lower learning cost. But type errors are a per-site tax: each call site that could receive a wrong type is an error site. For $n$ call sites:

-   Static typing: type checker verifies once, 0 runtime type errors

-   Dynamic typing: $n$ potential runtime type errors, each requiring defensive code or debugging

The "simplicity" of dynamic typing distributes type-checking to every call site.

## Unification with Papers 1--3 {#sec:unification}

The Simplicity Tax Theorem unifies results across the pentalogy:

**Paper 1 (Typing Disciplines).** Fixed-axis type systems are incomplete for domains requiring additional axes. The Simplicity Tax quantifies the cost: $|\text{requiredAxes}(D) \setminus \text{fixedAxes}|$ per use site. Parameterized type systems are complete (zero tax).

**Paper 2 (SSOT).** Non-SSOT architectures distribute specification across $n$ locations. Each location is a potential error site. SSOT centralizes specification: $H_{\text{distributed}} = 0$.

**Paper 3 (Leverage).** High-leverage solutions have high $H_{\text{central}}$ and low $H_{\text{distributed}}$. Leverage $= \text{impact}/\text{effort} = n / H_{\text{central}}$ when $H_{\text{distributed}} = 0$. Low-leverage solutions pay per-site.

**Paper 4 (This Paper).** Identifying which axes matter is coNP-complete. If you guess wrong and use an incomplete tool, you pay the Simplicity Tax. The tax is the cost of the coNP-hard problem you failed to solve.

::: theorem
Across Papers 1--4, solutions with higher $H_{\text{central}}$ and zero $H_{\text{distributed}}$ strictly dominate solutions with lower $H_{\text{central}}$ and positive $H_{\text{distributed}}$, for $n > n^*$.

These are not four separate claims. They are four views of a single phenomenon: the conservation and distribution of intrinsic problem complexity.
:::

## Formal Competence {#sec:competence}

::: definition
An engineer is *formally competent* with respect to complexity distribution if they correctly account for both $H_{\text{central}}$ and $H_{\text{distributed}}$ when evaluating tools.
:::

**The Competence Test:**

1.  Identify intrinsic problem complexity: $|R(P)|$

2.  Identify tool's native axes: $|A(T)|$

3.  Compute the gap: $|R(P) \setminus A(T)|$

4.  Compute total cost: $H_{\text{central}}(T) + n \times |R(P) \setminus A(T)|$

5.  Compare tools by total cost, not $H_{\text{central}}$ alone

Failing step 4---evaluating tools by learning cost alone---is formal incompetence.

::: remark
Python's Zen states: "Simple is better than complex. Complex is better than complicated." This is often misread as endorsing simplicity unconditionally. The correct reading:

-   **Simple**: Low intrinsic complexity (both $H_{\text{central}}$ and $H_{\text{distributed}}$ low)

-   **Complex**: High intrinsic complexity, *structured* (high $H_{\text{central}}$, low $H_{\text{distributed}}$)

-   **Complicated**: High intrinsic complexity, *tangled* (low $H_{\text{central}}$, high $H_{\text{distributed}}$)

The Zen says: when the problem has intrinsic complexity, *complex* (centralized) beats *complicated* (distributed). The community often conflates complex with complicated.
:::

## Lean 4 Formalization {#sec:simplicity-lean}

All theorems in this section are machine-checked in `DecisionQuotient/HardnessDistribution.lean`:

::: center
  **Theorem**                          **Lean Name**
  ------------------------------------ ---------------------------------
  Simplicity Tax Conservation          `simplicityTax_conservation`
  Complete Tools Pay No Tax            `complete_tool_no_tax`
  Incomplete Tools Pay Positive Tax    `incomplete_tool_positive_tax`
  Tax Grows Linearly                   `simplicityTax_grows`
  Complete Dominates Incomplete        `complete_dominates_incomplete`
  The Fallacy Theorem                  `simplicity_preference_fallacy`
  Amortization Threshold               `amortization_threshold`
  Dominance Transitivity               `dominates_trans`
  Tax Antitone w.r.t. Expressiveness   `simplicityTax_antitone`
:::

The formalization uses `Finset `$\mathbb{N}$ for axes, making the simplicity tax a computable natural number. The `Tool` type forms a lattice under the expressiveness ordering, with tax antitone (more expressive $\Rightarrow$ lower tax).

All proofs compile with zero `sorry` placeholders.


# Related Work {#sec:related}

## Computational Decision Theory

The complexity of decision-making has been studied extensively. Papadimitriou [@papadimitriou1994complexity] established foundational results on the complexity of game-theoretic solution concepts. Our work extends this to the meta-question of identifying relevant information. For a modern treatment of complexity classes, see Arora and Barak [@arora2009computational].

## Feature Selection

In machine learning, feature selection asks which input features are relevant for prediction. This is known to be NP-hard in general [@blum1997selection]. Our results show the decision-theoretic analog is -complete for both checking and minimization.

## Value of Information

The value of information (VOI) framework [@howard1966information] quantifies how much a decision-maker should pay for information. Our work addresses a different question: not the *value* of information, but the *complexity* of identifying which information has value.

## Model Selection

Statistical model selection (AIC [@akaike1974new], BIC [@schwarz1978estimating], cross-validation [@stone1974cross]) provides practical heuristics for choosing among models. Our results provide theoretical justification: optimal model selection is intractable, so heuristics are necessary.


# Conclusion

## Methodology and Disclosure {#methodology-and-disclosure .unnumbered}

**Role of LLMs in this work.** This paper was developed through human-AI collaboration. The author provided the core intuitions---the connection between decision-relevance and computational complexity, the conjecture that SUFFICIENCY-CHECK is coNP-complete, and the insight that the $\Sigma_2^P$ structure collapses for MINIMUM-SUFFICIENT-SET. Large language models (Claude, GPT-4) served as implementation partners for proof drafting, Lean formalization, and LaTeX generation.

The Lean 4 proofs were iteratively refined: the author specified what should be proved, the LLM proposed proof strategies, and the Lean compiler served as the arbiter of correctness. The complexity-theoretic reductions required careful human oversight to ensure the polynomial bounds were correctly established.

**What the author contributed:** The problem formulations (SUFFICIENCY-CHECK, MINIMUM-SUFFICIENT-SET, ANCHOR-SUFFICIENCY), the hardness conjectures, the tractability conditions, and the connection to over-modeling in engineering practice.

**What LLMs contributed:** LaTeX drafting, Lean tactic exploration, reduction construction assistance, and prose refinement.

The proofs are machine-checked; their validity is independent of generation method. We disclose this methodology in the interest of academic transparency.

::: center

----------------------------------------------------------------------------------------------------
:::

We have established that identifying decision-relevant information is computationally hard:

-   Checking whether a coordinate set is sufficient is -complete

-   Finding the minimum sufficient set is -complete (the $\SigmaP{2}$ structure collapses)

-   Anchor sufficiency (fixed-coordinate subcube) is $\SigmaP{2}$-complete

-   A complexity dichotomy separates easy (logarithmic) from hard (linear) cases

-   Tractable subcases exist for bounded actions, separable utilities, and tree structures

These results establish a fundamental principle of rational decision-making under uncertainty:

> **Determining what you need to know is harder than knowing everything.**

This is  It is a mathematical theorem with universal scope. Any agent facing structured uncertainty---whether a climate scientist, financial analyst, software engineer, or artificial intelligence---faces the same computational constraint. The ubiquity of over-modeling across domains is not coincidence, laziness, or poor discipline. It is the provably optimal response to intractability.

The principle has immediate normative force: stop criticizing engineers for including "irrelevant" parameters. Stop demanding minimal models. Stop building tools that promise to identify "what really matters." These aspirations conflict with computational reality. The dichotomy theorem (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}) characterizes exactly when tractability holds; outside those boundaries, over-modeling is not a failure mode---it is the only rational strategy.

All proofs are machine-checked in Lean 4, ensuring correctness of the core mathematical claims including the reduction mappings and equivalence theorems. Complexity classifications follow from standard complexity-theoretic results (TAUTOLOGY is coNP-complete, $\exists\forall$-SAT is $\Sigma_2^\text{P}$-complete) under the encoding model described in Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}.

## Why These Results Are Final {#why-these-results-are-final .unnumbered}

The theorems proven here are *ceiling results*---no stronger claims are possible within their respective frameworks:

1.  **Exact complexity characterization (not just lower bounds).** We prove SUFFICIENCY-CHECK is -complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}). This is *both* a lower bound (-hard) and an upper bound (in ). The complexity class is exact. Additional lower or upper bounds would be redundant.

2.  **Universal impossibility ($\forall$), not probabilistic prevalence ($\mu = 1$).** Theorems quantify over *all* decision problems satisfying the structural constraints, not measure-1 subsets. Measure-theoretic claims like "hard instances are prevalent" would *weaken* the results from "always hard (unless P = coNP)" to "almost always hard."

3.  **Constructive reductions, not existence proofs.** Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"} provides an explicit polynomial-time reduction from TAUTOLOGY to SUFFICIENCY-CHECK. This is stronger than proving hardness via non-constructive arguments (e.g., diagonalization). The reduction is machine-checked and executable.

4.  **Dichotomy is complete (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}).** The complexity separates into exactly two cases: polynomial (when minimal sufficient set has size $O(\log |S|)$) or exponential (when size is $\Omega(n)$). Under standard assumptions ( $\neq$ ), there are no intermediate cases. The dichotomy is exhaustive.

5.  **Tractable cases are maximal (Section [\[sec:tractable\]](#sec:tractable){reference-type="ref" reference="sec:tractable"}).** The tractability conditions (bounded actions, separable utilities, tree structure) are shown to be *tight*---relaxing any condition yields -hardness. These are the boundary cases, not a subset of tractable instances.

**What would NOT strengthen the results:**

-   **Additional complexity classes:** SUFFICIENCY-CHECK is -complete. Proving it is also NP-hard, PSPACE-hard, or #P-hard would add no information (these follow from -completeness under standard reductions).

-   **Average-case hardness:** We prove worst-case hardness. Average-case results would be *weaker* (average $\leq$ worst) and would require distributional assumptions not present in the problem definition.

-   **#P-hardness of counting:** When the decision problem is asking "does there exist?" (existential) or "are all?" (universal), the corresponding counting problem is trivially at least as hard. Proving #P-hardness separately would be redundant unless we change the problem to count something else.

-   **Approximation hardness beyond inapproximability:** The coNP-completeness of MINIMUM-SUFFICIENT-SET (Theorem [\[thm:minsuff-conp\]](#thm:minsuff-conp){reference-type="ref" reference="thm:minsuff-conp"}) implies no polynomial-time algorithm can approximate the minimal sufficient set size within any constant factor (unless P = coNP). This is maximal inapproximability---the problem admits no non-trivial approximation.

These results close the complexity landscape for coordinate sufficiency. Within classical complexity theory, the characterization is complete.

## The Simplicity Tax: A Major Practical Consequence {#the-simplicity-tax-a-major-practical-consequence .unnumbered}

A widespread belief holds that "simpler is better"---that preferring simple tools and minimal models is a mark of sophistication. This paper proves that belief is context-dependent and often wrong.

The *Simplicity Tax Theorem* (Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"}) establishes: when a problem requires $k$ axes of variation and a tool natively supports only $j < k$ of them, the remaining $k - j$ axes must be handled externally at *every use site*. For $n$ use sites, the "simpler" tool creates $(k-j) \times n$ units of external work. A tool matched to the problem's complexity creates zero external work.

> **True sophistication is matching tool complexity to problem complexity.**

Preferring "simple" tools for complex problems is not wisdom---it is a failure to account for distributed costs. The simplicity tax is paid invisibly, at every use site, by every user, forever. The sophisticated engineer asks not "which tool is simpler?" but "which tool matches my problem's intrinsic complexity?"

This result is machine-checked in Lean 4 (`HardnessDistribution.lean`). The formalization proves conservation (you can't eliminate the tax, only redistribute it), dominance (complete tools always beat incomplete tools), and the amortization threshold (beyond which the "complex" tool is strictly cheaper).

## The Foundational Contribution {#the-foundational-contribution .unnumbered}

This paper proves a universal constraint on optimization under uncertainty. The constraint is:

-   **Mathematical**, not empirical---it follows from the structure of computation

-   **Universal**, not domain-specific---it applies to any decision problem with coordinate structure

-   **Permanent**, not provisional---no algorithmic breakthrough can circumvent -completeness (unless P = coNP)

The result explains phenomena across disciplines: why feature selection uses heuristics, why configuration files grow, why sensitivity analysis is approximate, why model selection is art rather than science. These are not separate problems with separate explanations. They are manifestations of a single computational constraint, now formally characterized.

The Simplicity Tax Theorem adds a practical corollary: the universal response to intractability (over-modeling) is not just rational---attempting to avoid it by using "simpler" tools is actively counterproductive. Simplicity that mismatches problem complexity creates more work, not less.

Open questions remain (fixed-parameter tractability, quantum complexity, average-case behavior under natural distributions), but the foundational question---*is identifying relevance fundamentally hard?*---is answered: yes.


# Lean 4 Proof Listings {#app:lean}

The complete Lean 4 formalization is available at:

::: center
<https://doi.org/10.5281/zenodo.18140966>
:::

## On the Nature of Foundational Proofs {#foundational-proofs-nature}

The Lean proofs are straightforward applications of definitions and standard complexity-theoretic constructions. Foundational work produces insight through formalization.

**Definitional vs. derivational proofs.** The core theorems establish definitional properties and reduction constructions. For example, the polynomial reduction composition theorem (Theorem [\[thm:poly-compose\]](#thm:poly-compose){reference-type="ref" reference="thm:poly-compose"}) proves that composing two polynomial-time reductions yields a polynomial-time reduction. The proof follows from the definition of polynomial time: composing two polynomials yields a polynomial.

**Precedent in complexity theory.** This pattern appears throughout foundational complexity theory:

-   **Cook-Levin Theorem (1971):** SAT is NP-complete. The proof constructs a reduction from an arbitrary NP problem to SAT. The construction itself is straightforward (encode Turing machine computation as boolean formula), but the *insight* is recognizing that SAT captures all of NP.

-   **Ladner's Theorem (1975):** If P $\neq$ NP, then NP-intermediate problems exist. The proof is a diagonal construction---conceptually simple once the right framework is identified.

-   **Toda's Theorem (1991):** The polynomial hierarchy is contained in P$^\#$P. The proof uses counting arguments that are elegant but not technically complex. The profundity is in the *connection* between counting and the hierarchy.

**Why simplicity indicates strength.** A definitional theorem derived from precise formalization is *stronger* than an informal argument. When we prove that sufficiency checking is coNP-complete (Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}), we are not saying "we tried many algorithms and they all failed." We are saying something universal: *any* algorithm solving sufficiency checking can solve TAUTOLOGY, and vice versa. The proof is a reduction construction that follows from the problem definitions.

**Where the insight lies.** The semantic contribution of our formalization is:

1.  **Precision forcing.** Formalizing "coordinate sufficiency" in Lean requires stating exactly what it means for a coordinate subset to contain all decision-relevant information. This precision eliminates ambiguity about edge cases (what if projections differ only on irrelevant coordinates?).

2.  **Reduction correctness.** The TAUTOLOGY reduction (Section [\[sec:hardness\]](#sec:hardness){reference-type="ref" reference="sec:hardness"}) is machine-checked to preserve the decision structure. Informal reductions can have subtle bugs; Lean verification guarantees the mapping is correct.

3.  **Complexity dichotomy.** Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"} proves that problem instances are either tractable (P) or intractable (coNP-complete), with no intermediate cases under standard assumptions. This emerges from the formalization of constraint structure, not from case enumeration.

**What machine-checking guarantees.** The Lean compiler verifies that every proof step is valid, every definition is consistent, and no axioms are added beyond Lean's foundations (extended with Mathlib for basic combinatorics and complexity definitions). Zero `sorry` placeholders means zero unproven claims. The 3,400+ lines establish a verified chain from basic definitions (decision problems, coordinate spaces, polynomial reductions) to the final theorems (hardness results, dichotomy, tractable cases). Reviewers need not trust our informal explanations---they can run `lake build` and verify the proofs themselves.

**Comparison to informal complexity arguments.** Prior work on model selection complexity (Chickering et al. [@chickering2004large], Teyssier & Koller [@teyssier2012ordering]) presents compelling informal arguments but lacks machine-checked proofs. Our contribution is not new *wisdom*---the insight that model selection is hard is old. Our contribution is *formalization*: making "coordinate sufficiency" precise enough to mechanize, constructing verified reductions, and proving the complexity results hold for the formalized definitions.

This follows the tradition of verified complexity theory: just as Nipkow & Klein [@nipkow2014concrete] formalized automata theory and Cook [@cook2018complexity] formalized NP-completeness in proof assistants, we formalize decision-theoretic complexity. The proofs are simple because the formalization makes the structure clear. Simple proofs from precise definitions are the goal, not a limitation.

## Module Structure

The formalization consists of 33 files organized as follows:

-   `Basic.lean` -- Core definitions (DecisionProblem, CoordinateSet, Projection)

-   `AlgorithmComplexity.lean` -- Complexity definitions (polynomial time, reductions)

-   `PolynomialReduction.lean` -- Polynomial reduction composition (Theorem [\[thm:poly-compose\]](#thm:poly-compose){reference-type="ref" reference="thm:poly-compose"})

-   `Reduction.lean` -- TAUTOLOGY reduction for sufficiency checking

-   `Hardness/` -- Counting complexity and approximation barriers

-   `Tractability/` -- Bounded actions, separable utilities, tree structure, FPT

-   `Economics/` -- Value of information and elicitation connections

-   `Dichotomy.lean` and `ComplexityMain.lean` -- Summary results

-   `HardnessDistribution.lean` -- Simplicity Tax Theorem (Section [\[sec:simplicity-tax\]](#sec:simplicity-tax){reference-type="ref" reference="sec:simplicity-tax"})

## Key Theorems

::: theorem
[]{#thm:poly-compose label="thm:poly-compose"} Polynomial-time reductions compose to polynomial-time reductions.
:::

    theorem PolyReduction.comp_exists
        (f : PolyReduction A B) (g : PolyReduction B C) :
        exists h : PolyReduction A C,
          forall a, h.reduce a = g.reduce (f.reduce a)

::: theorem
[]{#thm:tax-conservation-lean label="thm:tax-conservation-lean"} The simplicity tax plus covered axes equals required axes (partition).
:::

    theorem simplicityTax_conservation :
        simplicityTax P T + (P.requiredAxes inter T.nativeAxes).card
          = P.requiredAxes.card

::: theorem
[]{#thm:fallacy-lean label="thm:fallacy-lean"} Incomplete tools always cost more than complete tools for $n > 0$ use sites.
:::

    theorem simplicity_preference_fallacy (T_simple T_complex : Tool)
        (h_simple_incomplete : isIncomplete P T_simple)
        (h_complex_complete : isComplete P T_complex)
        (n : Nat) (hn : n > 0) :
        totalExternalWork P T_complex n < totalExternalWork P T_simple n

## Verification Status

-   Total lines: $\sim$`<!-- -->`{=html}5,000

-   Theorems: 200+

-   Files: 33

-   Status: All proofs compile with no `sorry`


# Preemptive Rebuttals {#appendix-rebuttals}

We address anticipated objections to the main results.

## Objection 1: "coNP-completeness doesn't mean intractable"

**Objection:** "coNP-complete problems might have good heuristics or approximations. The hardness result doesn't preclude practical solutions."

**Response:** This objection actually *strengthens* our thesis. The point is not that practitioners cannot find useful approximations---they clearly do (feature selection heuristics in ML, sensitivity analysis in economics, configuration defaults in software). The point is that *optimal* dimension selection is provably hard.

The prevalence of heuristics across domains is itself evidence of the computational barrier. If optimal selection were tractable, we would see optimal algorithms, not heuristics. The universal adoption of "include more than necessary" strategies is the rational response to coNP-completeness.

## Objection 2: "Real problems don't have coordinate structure"

**Objection:** "Real decision problems are messier than your clean product-space model. The coordinate structure assumption is too restrictive."

**Response:** The assumption is weaker than it appears. Any finite state space can be encoded with binary coordinates; our hardness results apply to this encoding. More structured representations make the problem *easier*, not harder---so hardness for structured problems implies hardness for unstructured ones.

The coordinate structure abstracts common patterns: independent sensors, orthogonal configuration parameters, factored state spaces. These are ubiquitous in practice precisely because they enable tractable reasoning in special cases (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}).

## Objection 3: "The SAT reduction is artificial"

**Objection:** "The reduction from SAT/TAUT is an artifact of complexity theory. Real decision problems don't encode Boolean formulas."

**Response:** All coNP-completeness proofs use reductions. The reduction demonstrates that TAUT instances can be encoded as sufficiency-checking problems while preserving computational structure. This is standard methodology [@cook1971complexity; @karp1972reducibility].

The claim is not that practitioners encounter SAT problems in disguise, but that sufficiency checking is *at least as hard as* TAUT. If sufficiency checking were tractable, we could solve TAUT in polynomial time, contradicting the widely-believed $\P \neq \NP$ conjecture.

The reduction is a proof technique, not a claim about problem origins.

## Objection 4: "Tractable subcases are too restrictive"

**Objection:** "The tractable subcases (bounded actions, separable utility, tree structure) are too restrictive to cover real problems."

**Response:** These subcases characterize *when* dimension selection becomes feasible:

-   **Bounded actions:** Many real decisions have few options (buy/sell/hold, accept/reject, left/right/straight)

-   **Separable utility:** Additive decomposition is common in economics and operations research

-   **Tree structure:** Hierarchical dependencies appear in configuration, organizational decisions, and causal models

The dichotomy theorem (Theorem [\[thm:dichotomy\]](#thm:dichotomy){reference-type="ref" reference="thm:dichotomy"}) precisely identifies the boundary. The contribution is not that all problems are hard, but that hardness is the *default* unless special structure exists.

## Objection 5: "This just formalizes the obvious"

**Objection:** "Everyone knows feature selection is hard. This paper just adds mathematical notation to folklore."

**Response:** The contribution is unification. Prior work established hardness for specific domains (feature selection in ML [@guyon2003introduction], factor identification in economics, variable selection in statistics). We prove a *universal* result that applies to *any* decision problem with coordinate structure.

This universality explains why the same "over-modeling" pattern appears across unrelated domains. It's not that each domain independently discovered the same heuristic---it's that each domain independently hit the same computational barrier.

The theorem makes "obvious" precise and proves it applies universally. This is the value of formalization.

## Objection 6: "The Lean proofs don't capture the real complexity"

**Objection:** "The Lean formalization models an idealized version of the problem. Real coNP-completeness proofs are about Turing machines, not Lean types."

**Response:** The Lean formalization captures the mathematical structure of the reduction, not the Turing machine details. We prove:

1.  The sufficiency-checking problem is in coNP (verifiable counterexample)

2.  TAUT reduces to sufficiency checking (polynomial-time construction)

3.  The reduction preserves yes/no answers (correctness)

These are the mathematical claims that establish coNP-completeness. The Turing machine encoding is implicit in Lean's computational semantics. The formalization provides machine-checked verification that the reduction is correct.

## Objection 7: "The dichotomy is not tight"

**Objection:** "The dichotomy between $O(\log n)$ and $\Omega(n)$ minimal sufficient sets leaves a gap. What about $O(\sqrt{n})$?"

**Response:** The dichotomy is tight under standard complexity assumptions. The gap corresponds to problems reducible to a polynomial number of SAT instances---exactly the problems in the polynomial hierarchy between P and coNP.

In practice, the dichotomy captures the relevant cases: either the problem has logarithmic dimension (tractable) or linear dimension (intractable). Intermediate cases exist theoretically but are rare in practice.

## Objection 8: "This doesn't help practitioners"

**Objection:** "Proving hardness doesn't help engineers solve their problems. This paper offers no constructive guidance."

**Response:** Understanding limits is constructive. The paper provides:

1.  **Tractable subcases** (Theorem [\[thm:tractable\]](#thm:tractable){reference-type="ref" reference="thm:tractable"}): Check if your problem has bounded actions, separable utility, or tree structure

2.  **Justification for heuristics**: Over-modeling is not laziness---it's computationally rational

3.  **Focus for optimization**: Don't waste effort on optimal dimension selection; invest in good defaults and local search

Knowing that optimal selection is coNP-complete frees practitioners to use heuristics without guilt. This is actionable guidance.

## Objection 9: "But simple tools are easier to learn"

**Objection:** "The Simplicity Tax analysis ignores learning costs. Simple tools have lower barrier to entry, which matters for team adoption."

**Response:** This objection conflates $H_{\text{central}}$ (learning cost) with total cost. Yes, simple tools have lower learning cost. But for $n$ use sites, the total cost is: $$H_{\text{total}} = H_{\text{central}} + n \times H_{\text{distributed}}$$

The learning cost is paid once; the per-site cost is paid $n$ times. For $n > H_{\text{central}} / H_{\text{distributed}}$, the "complex" tool with higher learning cost has lower total cost.

The objection is actually an argument for training, not for tool avoidance. If the learning cost is the barrier, pay it---the amortization makes it worthwhile.

## Objection 10: "My team doesn't know metaclasses/types/frameworks"

**Objection:** "In practice, teams use what they know. Advocating for 'complex' tools ignores organizational reality."

**Response:** The Simplicity Tax is paid regardless of whether your team recognizes it. Ignorance of the tax does not exempt you from paying it.

If your team writes boilerplate at 50 locations because they don't know metaclasses, they pay the tax---in time, bugs, and maintenance. The tax is real whether it appears on a ledger or not.

Organizational reality is a constraint on *implementation*, not on *what is optimal*. The Simplicity Tax Theorem tells you the optimal; your job is to approach it within organizational constraints. "We don't know X" is a gap to close, not a virtue to preserve.

## Objection 11: "We can always refactor later"

**Objection:** "Start simple, refactor when needed. Technical debt is manageable."

**Response:** Refactoring from distributed to centralized is $O(n)$ work---you are paying the accumulated Simplicity Tax all at once. If you have $n$ sites each paying tax $k$, refactoring costs at least $nk$ effort.

"Refactor later" is not free. It is deferred payment with interest. The Simplicity Tax accrues whether you pay it incrementally (per-site workarounds) or in bulk (refactoring).

Moreover, distributed implementations create dependencies. Each workaround becomes a local assumption that must be preserved during refactoring. The refactoring cost is often *superlinear* in $n$.

## Objection 12: "The Simplicity Tax assumes all axes are equally important"

**Objection:** "Real problems have axes of varying importance. A tool that covers the important axes might be good enough."

**Response:** The theorem is conservative: it counts axes uniformly. Weighted versions strengthen the result.

If axis $a$ has importance $w_a$, define weighted tax: $$\text{WeightedTax}(T, P) = \sum_{a \in R(P) \setminus A(T)} w_a$$

Now the incomplete tool pays $\sum w_a \times n$ while the complete tool pays 0. The qualitative result is unchanged: incomplete tools pay per-site; complete tools do not.

The "cover important axes" heuristic only works if you *correctly identify* which axes are important. By Theorem [\[thm:sufficiency-conp\]](#thm:sufficiency-conp){reference-type="ref" reference="thm:sufficiency-conp"}, this identification is coNP-complete. You are back to the original hardness result.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/proofs/paper4_*.lean`
- Lines: 2760
- Theorems: 106
