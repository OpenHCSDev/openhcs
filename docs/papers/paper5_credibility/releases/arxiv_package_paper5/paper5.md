# Paper: A Formal Theory of Credibility: Why Assertions of Trustworthiness Decrease Trust

**Status**: Draft-ready | **Lean**: 2057 lines, 82 theorems

---

## Abstract

A counterintuitive phenomenon pervades epistemic communication: emphatic assertions of trustworthiness often *decrease* perceived trustworthiness. "Trust me" invites suspicion; excessive qualification triggers doubt rather than alleviating it. This paper provides the first formal framework explaining this phenomenon through the lens of signaling theory.

**Theorem (Cheap Talk Bound).** For any signal $s$ whose production cost is truth-independent, posterior credibility is bounded: $\Pr[C{=}1 \mid s] \leq p/(p + (1-p)q)$, where $p$ is the prior and $q$ is the mimicability of the signal. Verbal assertions---including assertions about credibility---are cheap talk and therefore subject to this bound.

**Theorem (Emphasis Penalty).** There exists a threshold $k^*$ such that for $n > k^*$ repeated assertions of claim $c$: $\partial C(c, s_{1..n})/\partial n < 0$. Additional emphasis *decreases* credibility, as excessive signaling is itself informative of deceptive intent.

**Theorem (Text Credibility Bound).** For high-magnitude claims (low prior probability), no text string achieves credibility above threshold $\tau < 1$. This is an impossibility result: rephrasing cannot escape the cheap talk bound.

**Theorem (Costly Signal Escape).** Signals with truth-dependent costs---where $\text{Cost}(s \mid \text{false}) > \text{Cost}(s \mid \text{true})$---can achieve arbitrarily high credibility as the cost differential increases. Machine-checked proofs are maximally costly signals: producing a compiling proof of a false theorem has infinite cost.

These results integrate with the leverage framework (Paper 3): credibility leverage $L_C = \Delta C / \text{Signal Cost}$ is maximized by minimizing cheap talk and maximizing costly signal exposure. Claims are regime-typed by channel (`[CT]` cheap-talk, `[VS]` verifier-backed) and audience domain (`[M]`, `[S]`). The theorems are formalized in Lean 4.

**Keywords:** signaling theory, cheap talk, credibility, Bayesian epistemology, costly signals, formal verification, Lean 4


# Introduction

A puzzling phenomenon occurs in human and human-AI communication: emphatic assertions of trustworthiness often *reduce* perceived trustworthiness. "Trust me" invites suspicion. "I'm not lying" suggests deception. Excessive qualification of claims triggers doubt rather than alleviating it [@grice1975logic].

This paper provides the first formal framework for understanding this phenomenon. Our central thesis:

> **Credibility is bounded by signal cost. Assertions with truth-independent production costs cannot shift rational priors beyond computable thresholds.**

## The Credibility Paradox

**Observation:** Let $C(s)$ denote credibility assigned to statement $s$. For assertions $a$ about credibility itself:

$$\frac{\partial C(s \cup a)}{\partial |a|} < 0 \text{ past threshold } \tau$$

Adding more credibility-assertions *decreases* total credibility. This is counterintuitive under naive Bayesian reasoning but empirically robust, as explored in foundational models of reputation and trust [@sobel1985theory; @grice1975logic].

**Examples:** - "This is absolutely true, I swear" \< "This is true" \< stating the claim directly - Memory containing "verified, don't doubt, proven" triggers more skepticism than bare facts - Academic papers with excessive self-citation of rigor invite reviewer suspicion

## Core Insight: Cheap Talk Bounds

The resolution comes from signaling theory [@spence1973job; @crawford1982strategic]. Define:

**Cheap Talk:** A signal $s$ is *cheap talk* if its production cost is independent of its truth value: $\text{Cost}(s | \text{true}) = \text{Cost}(s | \text{false})$

**Theorem (Informal):** Cheap talk cannot shift rational priors beyond bounds determined by the prior probability of deception [@farrell1996cheap; @crawford1982strategic].

Verbal assertions---including assertions about credibility---are cheap talk. A liar can say "I'm trustworthy" as easily as an honest person. Therefore, such assertions provide bounded evidence.

## Connection to Leverage

This paper extends the leverage framework (Paper 3) [@paper3_leverage] to epistemic domains. While Paper 4 characterizes the computational hardness of deciding which information to model [@paper4_decisionquotient], this paper characterizes the epistemic bounds of communicating that information.

**Credibility Leverage:** $L_C = \frac{\Delta \text{Credibility}}{\text{Signal Cost}}$

-   Cheap talk: Cost $\approx 0$, but $\Delta C$ bounded $\to L_C$ finite but capped

-   Costly signals: Cost \> 0 and truth-dependent $\to L_C$ can be unbounded

-   Meta-assertions: Cost = 0, subject to recursive cheap talk bounds

## Contributions

1.  **Formal Framework (Section 2):** Rigorous definitions of signals, costs, credibility functions, and rationality constraints.

2.  **Cheap Talk Theorems (Section 3):**

    -   Theorem 3.1: Cheap Talk Bound

    -   Theorem 3.2: Magnitude Penalty (credibility decreases with claim magnitude)

    -   Theorem 3.3: Emphasis Penalty (excessive assertion decreases credibility)

    -   Theorem 3.4: Meta-Assertion Trap (recursive bound on assertions about assertions)

3.  **Costly Signal Characterization (Section 4):**

    -   Definition of truth-dependent costs

    -   Theorem 4.1: Costly signals can shift priors unboundedly

    -   Theorem 4.2: Cost-credibility equivalence

4.  **Impossibility Results (Section 5):**

    -   Theorem 5.1: No string achieves credibility above threshold for high-magnitude claims

    -   Corollary: Memory phrasing cannot solve credibility problems

5.  **Leverage Integration (Section 6):** Credibility as DOF minimization; optimal signaling strategies.

6.  **Machine-Checked Proofs (Appendix):** All theorems formalized in Lean 4 [@demoura2021lean4; @mathlib2020].

**Claim typing.** As in Paper 4, strong claims are typed by regime rather than asserted globally: cheap-talk channel claims (`[CT]`), verified-signal claims (`[VS]`), and domain-specific audience claims (`[M]` mathematical, `[S]` social). Applied recommendations are valid only in the tagged regime where the theorem is proved.

## Anticipated Objections {#sec:objection-summary}

Before proceeding, we address objections readers are likely forming. Each is refuted in detail in Appendix [\[appendix-rebuttals\]](#appendix-rebuttals){reference-type="ref" reference="appendix-rebuttals"}.

#### "Signaling theory is old---this isn't novel."

Spence's signaling model [@spence1973job] and Crawford-Sobel's cheap talk [@crawford1982strategic] are foundational. Our contribution is (1) applying these to *meta-assertions* (claims about credibility), (2) proving *computable bounds* on credibility gain, and (3) integrating with the leverage framework. The theorems are new; the foundations are established.

#### "Real communication doesn't follow Bayesian rationality."

The rationality assumption is an idealization that provides upper bounds. If agents deviate from Bayesian reasoning, credibility bounds may be tighter, not looser. The theorems characterize what is *achievable* under optimal reasoning---a ceiling, not a prediction.

#### "Costly signals aren't always truth-dependent."

Correct. The definition (Section 2) distinguishes truth-dependent costs (credibility-enhancing) from truth-independent costs (not credibility-enhancing). Expensive signals that are equally costly for liars and truth-tellers remain cheap talk despite their cost.

#### "The magnitude penalty seems wrong---detailed claims are more credible."

Detail *about the claim* can be credibility-enhancing (costly signal: research effort). Detail *about credibility itself* is cheap talk and subject to the magnitude penalty. The theorem distinguishes signal content from signal cost.

#### "The Lean proofs are just type-checking, not real mathematics."

The Lean proofs formalize the mathematical structure of signaling theory. They verify that the cheap talk bounds follow from the definitions. The contribution is machine-checked precision, not computational complexity.

**If you have an objection not listed above,** check Appendix [\[appendix-rebuttals\]](#appendix-rebuttals){reference-type="ref" reference="appendix-rebuttals"} before concluding it has not been considered.

::: center

----------------------------------------------------------------------------------------------------
:::


# Foundations

## Two Credibility Domains

This paper distinguishes two fundamentally different credibility domains that obey different dynamics:

**Definition 2.0a (Mathematical Credibility).** *Mathematical credibility* $C_M$ measures the probability that a claim is logically sound. The audience is a formal verifier (proof assistant, compiler, test suite). The signal space consists of artifacts that can be mechanically checked. Mathematical credibility is binary at the limit: a proof compiles or it doesn't.

**Definition 2.0b (Social Credibility).** *Social credibility* $C_S$ measures the probability that a social audience accepts a claim. The audience is human agents with priors shaped by institutional hierarchy, reputation, and group membership. The signal space consists of credentials, affiliations, endorsements, and communication patterns.

**Theorem 2.0c (Domain Independence).** Mathematical credibility and social credibility are orthogonal: $$C_M(c, s) \not\Rightarrow C_S(c, s) \quad \text{and} \quad C_S(c, s) \not\Rightarrow C_M(c, s)$$ A signal maximizing one domain does not necessarily affect the other.

*Proof.* Constructive. (1) High $C_M$, low $C_S$: a correct proof by an unknown author receives $C_M \to 1$ (it compiles) but may receive $C_S \approx P_{\text{prior}}$ (no institutional endorsement). (2) High $C_S$, low $C_M$: a claim by a prestigious institution without formal verification receives high $C_S$ (reputation transfer) but $C_M$ is undefined or low (no proof). 0◻

**Corollary 2.0d (Costly Signal Domain-Specificity).** Costly signals are domain-specific:

-   Machine-checked proofs are maximally costly in the mathematical domain (cannot compile a false proof) but may be cheap talk in the social domain (anyone can claim to have proofs).

-   Institutional credentials (PhD, tenure, affiliation) are costly in the social domain (years of compliance) but cheap talk in the mathematical domain (credential $\not\Rightarrow$ soundness).

**Remark (Credibility Domain Conflict).** When a signal achieves $C_M \to 1$ but $C_S \approx 0$, the mathematical and social domains are in conflict. A rational response in the mathematical domain (engage with proofs) differs from a rational response in the social domain (defer to hierarchy). Observers may respond in either domain. This paper's theorems apply within each domain separately; cross-domain dynamics require modeling both simultaneously.

## Dual Truth Framework

This paper introduces a dual truth framework that distinguishes between objective validity and subjective acceptance:

**Definition 2.0e (Epistemic Truth, $E$).** *Epistemic truth* measures the probability that a claim corresponds to objective reality or logical truth. It is measurable via empirical evidence, logical proof, or formal verification. Range: $E \in [0, 1]$, where $E = 1$ indicates absolute truth and $E = 0$ indicates absolute falsity. Properties: objective, verifiable, independent of observer.

**Definition 2.0f (Ego-Driven Truth, $G$).** *Ego-driven truth* measures the probability that a claim aligns with an agent's self-interest, beliefs, or identity. It is measurable via incentive analysis, bias detection, or psychological modeling. Range: $G \in [0, 1]$, where $G = 1$ indicates perfect alignment and $G = 0$ indicates complete contradiction. Properties: subjective, observer-dependent, context-sensitive.

**Definition 2.0g (Truth Vector).** The *truth vector* is a 2D vector: $$\vec{T} = (E, G) \in [0, 1]^2$$ representing both the objective validity and subjective acceptance of a claim. This vector captures the dual nature of truth in epistemic communication.

**Theorem 2.0h (Truth Orthogonality).** Epistemic truth and ego-driven truth are orthogonal dimensions: $$E \perp G \quad \text{(no direct causal relationship)}$$ A change in one dimension does not necessarily affect the other. This orthogonality is analogous to the independence of mathematical and social credibility domains.

*Proof.* Constructive. (1) High $E$, low $G$: a scientifically proven fact that contradicts an agent's deeply held beliefs (e.g., climate change for a fossil fuel executive). (2) Low $E$, high $G$: a comforting lie that aligns perfectly with an agent's self-interest (e.g., \"I'm a great driver\" despite poor performance). 0◻

**Corollary 2.0i (Truth Tradeoff).** For high-magnitude claims (low prior probability), there exists a threshold where increasing epistemic truth decreases ego-driven truth and vice versa: $$\exists k^* \in [0,1] : \forall E > k^* \implies \frac{\partial G}{\partial E} < 0$$

## Signals and Costs

**Definition 2.1 (Signal).** A *signal* is a tuple $s = (c, v, p)$ where: - $c$ is the *content* (what is communicated) - $v \in \{\top, \bot\}$ is the *truth value* (whether content is true) - $p : \mathbb{R}_{\geq 0}$ is the *production cost*

**Definition 2.2 (Cheap Talk).** A signal $s$ is *cheap talk* if production cost is truth-independent: $$\text{Cost}(s | v = \top) = \text{Cost}(s | v = \bot)$$

**Definition 2.3 (Costly Signal).** A signal $s$ is *costly* if: $$\text{Cost}(s | v = \bot) > \text{Cost}(s | v = \top)$$ Producing the signal when false costs more than when true.

**Intuition:** Verbal assertions are cheap talk---saying "I'm honest" costs the same whether you're honest or not. A PhD from MIT is a costly signal [@spence1973job]---obtaining it while incompetent is much harder than while competent. Similarly, price and advertising can serve as signals of quality [@milgrom1986price].

## Credibility Functions

**Definition 2.4 (Prior).** A *prior* is a probability distribution $P : \mathcal{C} \to [0,1]$ over claims, representing beliefs before observing signals.

**Definition 2.5 (Credibility Function).** A *credibility function* is a mapping: $$C : \mathcal{C} \times \mathcal{S}^* \to [0,1]$$ from (claim, signal-sequence) pairs to credibility scores, satisfying: 1. $C(c, \emptyset) = P(c)$ (base case: prior) 2. Bayesian update: $C(c, s_{1..n}) = P(c | s_{1..n})$

**Definition 2.6 (Rational Agent).** An agent is *rational* if: 1. Updates beliefs via Bayes' rule 2. Has common knowledge of rationality [@aumann1995backward] (knows others are rational, knows others know, etc.) 3. Accounts for strategic signal production [@cho1987signaling].

## Deception Model

**Definition 2.7 (Deception Prior).** Let $\pi_d \in [0,1]$ be the prior probability that a random agent will produce deceptive signals. This is common knowledge.

**Definition 2.8 (Magnitude).** The *magnitude* of a claim $c$ is: $$M(c) = -\log P(c)$$ High-magnitude claims have low prior probability. This is the standard self-information measure [@shannon1948].

## Model Contract and Regime Tags {#sec:credibility-contract}

All theorem statements in this paper are typed by the following contract:

-   **K1 (binary claim state):** claim truth is modeled as $C \in \{0,1\}$.

-   **K2 (Bayesian receiver):** posterior credibility is computed by Bayes updates.

-   **K3 (signal channel declaration):** each theorem declares whether the signal channel is cheap talk or verifier-backed.

-   **K4 (audience domain declaration):** each theorem declares mathematical-domain ($C_M$) or social-domain ($C_S$) scope.

We use the following regime tags:

-   `[CT]`: cheap-talk channel (truth-independent signal cost),

-   `[VS]`: verifier-backed signal channel ($\varepsilon_T,\varepsilon_F$ model),

-   `[M]`: mathematical credibility domain,

-   `[S]`: social credibility domain,

-   `[D]`: dual-truth vector extensions ($E,G$).

::: proposition
[]{#prop:credibility-regime-coverage label="prop:credibility-regime-coverage"} Each declared regime above has at least one theorem-level mechanized core in Lean: `[CT]` via `cheap_talk_bound`, `magnitude_penalty`, `emphasis_penalty`; `[VS]` via `verified_signal_credibility`, `proof_as_ultimate_signal`; `[M]/[S]` via `domain_independence_math_not_implies_social` and `domain_independence_social_not_implies_math`.
:::

::: proof
*Proof.* Direct by inspection of the theorem declarations in `Credibility/CheapTalk.lean`, `Credibility/CostlySignals.lean`, and `Credibility/Basic.lean`. ◻
:::

::: center

----------------------------------------------------------------------------------------------------
:::


# Cheap Talk Theorems

## The Cheap Talk Bound

::: theorem
[]{#thm:cheap-talk-bound label="thm:cheap-talk-bound"} Let $C\in\{0,1\}$ denote the truth of a claim ($C=1$ true), with prior $p := \Pr[C=1]\in(0,1)$. Let $S$ be the event that the receiver observes a particular message-pattern (signal) $s$.

`Credibility.cheap_talk_bound` `Credibility.CheapTalk.cheapTalkBound`

Define the emission rates $$\alpha := \Pr[S \mid C=1],\qquad \beta := \Pr[S \mid C=0].$$ Then the posterior credibility of the claim given observation of $s$ is $$\Pr[C=1 \mid S] \;=\; \frac{p\,\alpha}{p\,\alpha + (1-p)\,\beta}.$$ Equivalently, in odds form, $$\frac{\Pr[C=1 \mid S]}{\Pr[C=0 \mid S]}
\;=\;
\frac{p}{1-p}\cdot \frac{\alpha}{\beta}.$$

In particular, if $s$ is a *cheap-talk* pattern in the sense that:

1.  truthful senders emit $s$ with certainty ($\alpha=1$), and

2.  deceptive senders can mimic $s$ with probability at least $q$ (i.e. $\beta \ge q$),

then credibility obeys the tight upper bound $$\Pr[C=1 \mid S] \;\le\; \frac{p}{p+(1-p)q}.$$ Moreover this bound is *tight*: equality holds whenever $\alpha=1$ and $\beta=q$.
:::

::: proof
*Proof.* By Bayes' rule, $$\Pr[C=1 \mid S]
= \frac{\Pr[S\mid C=1]\Pr[C=1]}{\Pr[S\mid C=1]\Pr[C=1] + \Pr[S\mid C=0]\Pr[C=0]}
= \frac{p\alpha}{p\alpha+(1-p)\beta}.$$ If $\alpha=1$ and $\beta \ge q$, the denominator is minimized by setting $\beta=q$, yielding $$\Pr[C=1 \mid S]\le \frac{p}{p+(1-p)q}.$$ Tightness is immediate when $\beta=q$. ◻
:::

**Remark (Notation reconciliation).** In this paper we use $q$ to denote the *mimicability* of a cheap-talk signal: the probability that a deceptive sender successfully produces the same message pattern as a truthful sender. If one prefers to work with detection probability $\pi_d$ (the probability deception is detected), then $q = 1 - \pi_d$ and the bound becomes $\Pr[C=1 \mid S] \le p / (p + (1-p)(1-\pi_d))$.

**Interpretation:** No matter how emphatically you assert something, cheap talk credibility is capped. The cap depends on how likely deception is in the population.

## The Magnitude Penalty

::: theorem
[]{#thm:magnitude-penalty label="thm:magnitude-penalty"} For claims $c_1, c_2$ with $M(c_1) < M(c_2)$ (i.e., $p_1 := P(c_1) > p_2 := P(c_2)$) and identical cheap talk signals $s$ with mimicability $q$: $$\Pr[c_1 \mid S] > \Pr[c_2 \mid S]$$ Higher-magnitude claims receive less credibility from identical signals.

`Credibility.CheapTalk.magnitude_penalty` `Credibility.CheapTalk.cheapTalkBound_strictMono_prior`
:::

::: proof
*Proof.* From Theorem [\[thm:cheap-talk-bound\]](#thm:cheap-talk-bound){reference-type="ref" reference="thm:cheap-talk-bound"}, the bound $p/(p+(1-p)q)$ is strictly increasing in $p$ for fixed $q \in (0,1)$. Since $p_1 > p_2$, we have $\Pr[c_1 \mid S] > \Pr[c_2 \mid S]$. ◻
:::

**Interpretation:** Claiming you wrote one good paper gets more credibility than claiming you wrote four. The signal (your assertion) is identical; the prior probability differs.

## The Emphasis Penalty

::: theorem
[]{#thm:emphasis-penalty label="thm:emphasis-penalty"} Let $s_1, s_2, ..., s_n$ be cheap talk signals all asserting claim $c$. There exists $k^*$ such that for $n > k^*$: $$\frac{\partial C(c, s_{1..n})}{\partial n} < 0$$ Additional emphasis *decreases* credibility past a threshold.

`Credibility.CheapTalk.emphasis_penalty` `Credibility.CheapTalk.suspicion_mono` `Credibility.CheapTalk.credibilityWithEmphasis`
:::

::: proof
*Proof.* The key insight: excessive signaling is itself informative. Define the *suspicion function*: $$\sigma(n) = P(\text{deceptive} | n \text{ assertions})$$

Honest agents have less need to over-assert. Therefore: $$P(n \text{ assertions} | \text{deceptive}) > P(n \text{ assertions} | \text{honest}) \text{ for large } n$$

By Bayes' rule, $\sigma(n)$ is increasing in $n$ past some threshold.

Substituting into the credibility update: $$C(c, s_{1..n}) = \frac{P(c) \cdot (1 - \sigma(n))}{P(c) \cdot (1 - \sigma(n)) + (1 - P(c)) \cdot \sigma(n)}$$

This is decreasing in $\sigma(n)$, hence decreasing in $n$ for $n > k^*$. ◻
:::

**Interpretation:** "Trust me, I'm serious, this is absolutely true, I swear" is *less* credible than just stating the claim. The emphasis signals desperation.

## The Meta-Assertion Trap

::: theorem
[]{#thm:meta-assertion-trap label="thm:meta-assertion-trap"} Let $a$ be a cheap talk assertion and $m$ be a meta-assertion "assertion $a$ is credible." Then: $$C(c, a \cup m) \leq C(c, a) + \epsilon$$ where $\epsilon \to 0$ as common knowledge of rationality increases.

`Credibility.CheapTalk.meta_assertion_trap` `Credibility.CheapTalk.meta_assertion_decreases` `Credibility.CheapTalk.meta_assertion_boost_nonpositive`
:::

::: proof
*Proof.* Meta-assertion $m$ is itself cheap talk (costs nothing to produce regardless of truth). Therefore $m$ is subject to the Cheap Talk Bound (Theorem [\[thm:cheap-talk-bound\]](#thm:cheap-talk-bound){reference-type="ref" reference="thm:cheap-talk-bound"}).

Under common knowledge of rationality, agents anticipate that deceptive agents will produce meta-assertions. Therefore: $$P(m | \text{deceptive}) \approx P(m | \text{honest})$$

The signal provides negligible information; $\epsilon \to 0$. ◻
:::

**Interpretation:** "My claims are verified" is cheap talk about cheap talk. It doesn't escape the bound---it's *subject to* the bound recursively. Adding "really verified, I promise" makes it worse.

::: center

----------------------------------------------------------------------------------------------------
:::


# Costly Signal Characterization

## Definition and Properties

::: theorem
[]{#thm:costly-signal label="thm:costly-signal"} For costly signal $s$ with cost differential $\Delta = \text{Cost}(s | \bot) - \text{Cost}(s | \top) > 0$: $$\Pr[C=1 \mid S] \to 1 \text{ as } \Delta \to \infty$$ Costly signals can achieve arbitrarily high credibility.

`Credibility.CostlySignals.costly_dominates_cheap` `Credibility.CostlySignals.verified_signal_limit_one`
:::

::: proof
*Proof.* If $\Delta$ is large, deceptive agents cannot afford to produce $s$, so $\beta := \Pr[S \mid C=0] \to 0$ as $\Delta \to \infty$. Applying Theorem [\[thm:cheap-talk-bound\]](#thm:cheap-talk-bound){reference-type="ref" reference="thm:cheap-talk-bound"} with $\alpha = 1$: $$\Pr[C=1 \mid S] = \frac{p}{p + (1-p)\beta} \to 1 \text{ as } \beta \to 0.$$ ◻
:::

::: theorem
[]{#thm:dual-cost-signal label="thm:dual-cost-signal"} For dual-cost signal $s$ with epistemic cost differential $\Delta_E = \text{Cost}_E(s | E=0) - \text{Cost}_E(s | E=1) > 0$ and ego cost differential $\Delta_G = \text{Cost}_G(s | G=0) - \text{Cost}_G(s | G=1) > 0$: $$\Pr[\vec{T} \text{ coherent} \mid S] \to 1 \text{ as } \min(\Delta_E, \Delta_G) \to \infty$$ Dual-cost signals can achieve arbitrarily high credibility for coherent truth claims.
:::

::: proof
*Proof.* A dual-cost signal with both $\Delta_E > 0$ and $\Delta_G > 0$ is costly for two reasons: 1. Epistemically false claims have higher epistemic cost 2. Ego-conflicting claims have higher ego cost

For a claim to be deceptive in a coherent way, it would need to be both epistemically false and ego-aligned, but the high $\Delta_E$ makes this costly. For a claim to be ego-driven but epistemically true, the high $\Delta_G$ makes this costly. Thus, only coherent claims (both epistemically true and ego-aligned) can afford to produce the signal.

As $\min(\Delta_E, \Delta_G) \to \infty$, the probability of deceptive signals $\beta := \Pr[S \mid \vec{T} \text{ incoherent}] \to 0$. Applying the same Bayes update form as Theorem [\[thm:cheap-talk-bound\]](#thm:cheap-talk-bound){reference-type="ref" reference="thm:cheap-talk-bound"} to the coherence event: $$\Pr[\vec{T} \text{ coherent} \mid S] = \frac{p}{p + (1-p)\beta} \to 1 \text{ as } \beta \to 0.$$ ◻
:::

::: theorem
[]{#thm:verified-signal label="thm:verified-signal"} Let $C\in\{0,1\}$ with prior $p=\Pr[C=1]$. Suppose a verifier produces an acceptance event $A$ such that $$\Pr[A \mid C=1]\ge 1-\varepsilon_T,\qquad \Pr[A \mid C=0]\le \varepsilon_F,$$ for some $\varepsilon_T,\varepsilon_F\in[0,1]$. Then $$\Pr[C=1 \mid A]
\;\ge\;
\frac{p(1-\varepsilon_T)}{p(1-\varepsilon_T) + (1-p)\varepsilon_F}.$$ In particular, if $\varepsilon_F\to 0$ and $\varepsilon_T$ is bounded away from $1$, then $\Pr[C=1\mid A]\to 1$.

`Credibility.CostlySignals.verified_signal_credibility` `Credibility.CostlySignals.verifiedCredibilityBound`
:::

::: proof
*Proof.* Apply Theorem [\[thm:cheap-talk-bound\]](#thm:cheap-talk-bound){reference-type="ref" reference="thm:cheap-talk-bound"} with $S:=A$, $\alpha:=\Pr[A\mid C=1]$, $\beta:=\Pr[A\mid C=0]$, then use $\alpha\ge 1-\varepsilon_T$ and $\beta\le\varepsilon_F$. ◻
:::

**Remark.** This theorem provides the formal bridge to machine-checked proofs: Lean corresponds to a verifier where false claims have negligible acceptance probability ($\varepsilon_F \approx 0$, modulo trusted kernel assumptions). The completeness gap $\varepsilon_T$ captures the effort to construct a proof.

## Examples of Costly Signals

  Signal                 Cost if True       Cost if False                Credibility Shift
  ---------------------- ------------------ ---------------------------- -------------------
  PhD from MIT           years effort       years + deception risk       Moderate
  Working code           Development time   Same + it won't work         High
  Verified Lean proofs   Proof effort       Impossible (won't compile)   Maximum
  Verbal assertion       \~0                \~0                          Bounded

  Dual-Cost Signal           Epistemic Cost Differential   Ego Cost Differential   Coherence Credibility
  -------------------------- ----------------------------- ----------------------- -----------------------
  Public peer review         Refutation risk               Reputation damage       High
  Independent audit          Investigation cost            Legal liability         Very High
  Open-source contribution   Debugging effort              Community backlash      Moderate-High
  Personal apology           Humility cost                 Ego preservation cost   High

**Key insight:** Lean proofs with `0 sorry` are *maximally costly signals*. You cannot produce a compiling proof of a false theorem. The cost differential is infinite [@demoura2021lean4; @debruijn1970automath].

::: theorem
[]{#thm:proof-ultimate label="thm:proof-ultimate"} Let $s$ be a machine-checked proof of claim $c$. Then: $$\Pr[c \mid s] = 1 - \varepsilon$$ where $\varepsilon$ accounts only for proof assistant bugs.

`Credibility.CostlySignals.proof_as_ultimate_signal` `Credibility.CostlySignals.verified_signal_limit_one`
:::

::: proof
*Proof.* This is a special case of Theorem [\[thm:verified-signal\]](#thm:verified-signal){reference-type="ref" reference="thm:verified-signal"} with $\varepsilon_T \approx 0$ (proof exists if claim is true and provable) and $\varepsilon_F \approx 0$ (proof assistant soundness). See [@demoura2021lean4; @debruijn1970automath]. ◻
:::

::: center

----------------------------------------------------------------------------------------------------
:::


# Impossibility Results

## The Text Credibility Bound

::: theorem
[]{#thm:text-bound label="thm:text-bound"} For any text string $T$ (memory content, assertion, etc.) and high-magnitude claim $c$ with $M(c) > M^*$ (i.e., prior $p < e^{-M^*}$): $$\Pr[c \mid T] < \tau$$ where $\tau < 1$ is determined by the mimicability $q$ and $M^*$. No text achieves full credibility for exceptional claims.

`Credibility.Impossibility.text_credibility_bound` `Credibility.Impossibility.high_magnitude_credibility_small` `Credibility.Impossibility.memory_iteration_futility`
:::

::: proof
*Proof.* Text is cheap talk (production cost independent of truth). Apply Theorem [\[thm:cheap-talk-bound\]](#thm:cheap-talk-bound){reference-type="ref" reference="thm:cheap-talk-bound"} with prior $p = e^{-M^*}$ and mimicability $q$: $$\tau = \frac{p}{p + (1-p)q} = \frac{e^{-M^*}}{e^{-M^*} + (1 - e^{-M^*})q}$$ For $M^*$ large (low prior probability), $\tau \to 0$ regardless of $q > 0$. ◻
:::

**Corollary 5.2 (Memory Iteration Futility).** No rephrasing of memory content can achieve credibility above $\tau$ for high-magnitude claims. Iteration on text is bounded in effectiveness.

**Interpretation:** This is why we couldn't solve the credibility problem by editing memory text. The *structure* of the problem (text is cheap talk, claims are high-magnitude) guarantees bounded credibility regardless of phrasing.

## Optimal Strategies

::: theorem
[]{#thm:optimal-credibility-strategy label="thm:optimal-credibility-strategy"} For high-magnitude claims in regime `[CT]`+`[VS]`, an optimal strategy is:

1.  Minimize cheap talk (reduce emphasis and meta-assertions),

2.  Maximize costly-signal exposure (show work and verifiable artifacts),

3.  Enable costly-to-fake demonstration channels.

*(Lean anchor: `optimal_strategy_dominance`.)*
:::

::: proof
*Proof.* From Theorem [\[thm:text-bound\]](#thm:text-bound){reference-type="ref" reference="thm:text-bound"}, text-only updates are bounded for high-magnitude claims. From Theorem [\[thm:verified-signal\]](#thm:verified-signal){reference-type="ref" reference="thm:verified-signal"}, verifier-backed channels strictly improve achievable posterior credibility as false-positive rate decreases. Therefore optimal policy minimizes bounded channels and allocates effort to verifier-backed costly channels. ◻
:::

::: center

----------------------------------------------------------------------------------------------------
:::


# Leverage Integration

## Credibility as DOF Minimization

Applying the leverage framework (Paper 3) [@paper3_leverage]:

**Signal DOF:** Words in an assertion are degrees of freedom. Each word can be independently modified.

**Signal Leverage:** $L_S = \frac{\Delta C}{\text{Words}}$

::: theorem
[]{#thm:credibility-leverage label="thm:credibility-leverage"} For cheap-talk signals with nonnegative credibility impact, leverage is maximized by minimizing word count: $$\arg\max_s L_S(s) = \arg\min_s |s|$$ subject to conveying the claim.

`Credibility.Leverage.brevity_principle` `Credibility.Leverage.credibility_leverage_minimization` `Credibility.Leverage.leverage_inverse_effort`
:::

::: proof
*Proof.* With impact fixed and nonnegative, $L_S=\Delta C/\text{Words}$ is inverse-monotone in word count. Hence shorter valid signals weakly dominate longer ones in leverage. ◻
:::

**Interpretation:** Shorter, terser memory entries achieve higher credibility leverage than verbose explanations. "70k lines, deployed in 3 labs" beats lengthy justification.

## Optimal Memory Design

Given Theorems 5.1-5.3 and 6.1, optimal memory content should:

1.  **State facts without meta-justification** (reduces Emphasis Penalty)

2.  **Include verifiable anchors** (third-party deployments, citations)

3.  **Specify mechanism** (explains how exceptional output is achievable)

4.  **Direct behavioral calibration** (tell model how to act, not what to believe)

## Practical Applications

The dual truth framework has broad applications across domains where communication involves both epistemic truth and ego-driven truth:

### Scientific Communication

In scientific publishing, the peer review process serves as a dual-cost signal: - **Epistemic cost:** Authors must conduct rigorous experiments, analyze data, and write a detailed manuscript - **Ego cost:** Authors must subject their work to criticism and potential rejection by peers

A paper with multiple independent replications has higher coherence: - Epistemic truth: Results are reproducible - Ego truth: Authors' reputation is enhanced by independent validation

### Political Communication

Political speeches often exhibit low coherence between epistemic and ego-driven truth: - **Epistemic truth:** Objective facts about policy impacts - **Ego truth:** What the audience wants to hear to support the politician

Fact-checking serves as a costly signal that increases coherence by penalizing epistemic falsehoods.

### Climate Change Communication {#climate-communication}

Climate change denial exhibits high incoherence: - Epistemic truth: Scientific consensus on human-caused climate change - Ego truth: Economic or ideological interests that conflict with climate action

Climate scientists use dual-cost signals such as peer-reviewed papers and data sharing to increase coherence.

### Corporate Communication

Corporate social responsibility (CSR) reports can exhibit varying degrees of coherence: - **High coherence:** Companies that back up claims with transparent data and independent audits - **Low coherence:** Companies that use greenwashing (superficial claims without action)

Independent sustainability audits serve as dual-cost signals that increase credibility.

::: center

----------------------------------------------------------------------------------------------------
:::


# Related Work

**Signaling Theory:** Spence (1973) [@spence1973job] introduced costly signaling in job markets. Zahavi (1975) [@zahavi1975mate] applied it to biology (handicap principle). Akerlof (1970) [@akerlof1970market] established the foundational role of asymmetric information in market collapse. We formalize and extend to text-based communication.

**Cheap Talk:** Crawford & Sobel (1982) [@crawford1982strategic] analyzed cheap talk in game theory. Farrell (1987) [@farrell1987cheap] and Farrell & Rabin (1996) [@farrell1996cheap] further characterized the limits of unverified communication. We prove explicit bounds on credibility shift.

**Epistemic Logic:** Hintikka (1962) [@hintikka1962knowledge], Fagin et al. (1995) [@fagin1995reasoning] formalized knowledge and belief. We add signaling structure.

**Bayesian Persuasion:** Kamenica & Gentzkow (2011) [@kamenica2011bayesian] studied optimal information disclosure. Our impossibility results complement their positive results.

**Social Epistemology:** Goldman (1999) [@goldman1999social] and Hardwig (1991) [@hardwig1991trust] studied the social dimensions of knowledge. Our dual truth framework extends this to include ego-driven truth as a complement to epistemic truth.

**Cognitive Dissonance:** Festinger (1957) [@festinger1957theory] introduced cognitive dissonance theory, which explains how individuals resolve conflicts between beliefs and actions. Our coherence measure quantifies this dissonance as a gap between epistemic and ego-driven truth.

**Dual Process Theories:** Kahneman (2011) [@kahneman2011thinking] and Evans (2003) [@evans2003in; @two] distinguished between fast, intuitive thinking (System 1) and slow, deliberate thinking (System 2). Our dual truth framework aligns with this distinction: ego-driven truth often operates through System 1, while epistemic truth requires System 2 reasoning.

::: center

----------------------------------------------------------------------------------------------------
:::


# Conclusion

We have formalized why assertions of credibility can decrease perceived credibility, proved impossibility bounds on cheap talk, and characterized the structure of costly signals.

**Key results:** 1. Cheap talk credibility is bounded (Theorem 3.1) 2. Emphasis decreases credibility past threshold (Theorem 3.3) 3. Meta-assertions are trapped in the same bound (Theorem 3.4) 4. No text achieves full credibility for exceptional claims (Theorem 5.1) 5. Only costly signals (proofs, demonstrations) escape the bound (Theorem 4.1)

**Implications:** - Memory phrasing iteration has bounded effectiveness - Real-time demonstration is the optimal credibility strategy - Lean proofs are maximally costly signals (infinite cost differential)

## Methodology and Disclosure {#methodology-and-disclosure .unnumbered}

**Role of LLMs in this work.** This paper was developed through human-AI collaboration, and this disclosure is particularly apropos given the paper's subject matter. The author provided the core intuitions---the cheap talk bound, the emphasis paradox, the impossibility of achieving full credibility via text---while large language models (Claude, GPT-4) served as implementation partners for formalization, proof drafting, and LaTeX generation.

The Lean 4 proofs (2057 lines, 0 sorry placeholders) were iteratively developed: the author specified theorems, the LLM proposed proof strategies, and the Lean compiler verified correctness.

**What the author contributed:** The credibility framework itself, the cheap talk bound conjecture, the emphasis penalty insight, the connection to costly signaling theory, and the meta-observation that Lean proofs are maximally costly signals.

**What LLMs contributed:** LaTeX drafting, Lean tactic suggestions, Bayesian calculation assistance, and prose refinement.

**Meta-observation:** This paper was produced via the methodology it describes---intuition-driven, LLM-implemented---demonstrating in real-time the credibility dynamics it formalizes. The LLM-generated text is cheap talk; the Lean proofs are costly signals. The proofs compile; therefore the theorems are true, regardless of how the proof text was generated. This is the paper's own thesis applied to itself.

::: center

----------------------------------------------------------------------------------------------------
:::


# Appendix: Lean Formalization

## Verification Scope

All theorem-level claims in this paper are mapped to Lean declarations in `docs/papers/paper5_credibility/proofs/Credibility/*.lean`. The proof artifact is checked by running:

    cd docs/papers/paper5_credibility/proofs
    lake build

## Module Structure

    Credibility/
    |- Basic.lean            -- core definitions + domain-independence lemmas
    |- CheapTalk.lean        -- Theorems 3.1-3.4
    |- CostlySignals.lean    -- Theorems 4.1-4.4
    |- Impossibility.lean    -- Theorems 5.1-5.3 (+ asymptotic form)
    |- Leverage.lean         -- leverage theorems
    `- CoherentStopping.lean -- stopping/threshold bridge utilities

## Claim-to-Proof Mapping

  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
  **Paper Claim**                                                                                                                                            **Lean Handle(s)**                                                                                                                 **Tag**
  ---------------------------------------------------------------------------------------------------------------------------------------------------------- ---------------------------------------------------------------------------------------------------------------------------------- ---------------
  Theorem [\[thm:cheap-talk-bound\]](#thm:cheap-talk-bound){reference-type="ref" reference="thm:cheap-talk-bound"}                                           `cheap_talk_bound`, `cheap_talk_bound_tight`                                                                                       `[CT]`

  Theorem [\[thm:magnitude-penalty\]](#thm:magnitude-penalty){reference-type="ref" reference="thm:magnitude-penalty"}                                        `magnitude_penalty`                                                                                                                `[CT]`

  Theorem [\[thm:emphasis-penalty\]](#thm:emphasis-penalty){reference-type="ref" reference="thm:emphasis-penalty"}                                           `emphasis_penalty`                                                                                                                 `[CT]`

  Theorem [\[thm:meta-assertion-trap\]](#thm:meta-assertion-trap){reference-type="ref" reference="thm:meta-assertion-trap"}                                  `meta_assertion_trap`, `meta_assertion_bounded`                                                                                    `[CT]`

  Theorem [\[thm:costly-signal\]](#thm:costly-signal){reference-type="ref" reference="thm:costly-signal"}                                                    `costly_dominates_cheap`                                                                                                           `[VS]`

  Theorem [\[thm:verified-signal\]](#thm:verified-signal){reference-type="ref" reference="thm:verified-signal"}                                              `verified_signal_credibility`, `verified_signal_limit_one`                                                                         `[VS]`

  Theorem [\[thm:proof-ultimate\]](#thm:proof-ultimate){reference-type="ref" reference="thm:proof-ultimate"}                                                 `proof_as_ultimate_signal`                                                                                                         `[VS],[M]`

  Theorem [\[thm:text-bound\]](#thm:text-bound){reference-type="ref" reference="thm:text-bound"}                                                             `text_credibility_bound`, `asymptotic_impossibility`                                                                               `[CT]`

  Theorem [\[thm:optimal-credibility-strategy\]](#thm:optimal-credibility-strategy){reference-type="ref" reference="thm:optimal-credibility-strategy"}       `optimal_strategy_dominance`                                                                                                       `[CT]+[VS]`

  Theorem [\[thm:credibility-leverage\]](#thm:credibility-leverage){reference-type="ref" reference="thm:credibility-leverage"}                               `credibility_leverage_minimization`, `brevity_principle`                                                                           `[CT]`

  Proposition [\[prop:credibility-regime-coverage\]](#prop:credibility-regime-coverage){reference-type="ref" reference="prop:credibility-regime-coverage"}   `domain_independence_math_not_implies_social`, `domain_independence_social_not_implies_math`, `machine_proof_domain_specificity`   `[M],[S]`
  -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

## Current Proof Statistics

**Lean files:** 10\
**Lean lines:** 2057\
**Theorem/lemma statements:** 82\
**Sorry placeholders:** 0

::: center

----------------------------------------------------------------------------------------------------
:::


# Preemptive Rebuttals {#appendix-rebuttals}

We address anticipated objections to the credibility framework.

## Objection 1: "Signaling theory is old---this isn't novel"

**Objection:** "Spence's signaling model and Crawford-Sobel's cheap talk are decades old. This paper just applies existing theory."

**Response:** The foundations are established; the application is novel. Our contributions:

1.  **Meta-assertions:** We apply cheap talk bounds to *claims about credibility itself*---a recursive structure not analyzed in prior work

2.  **Computable bounds:** We derive explicit formulas for credibility ceilings as functions of prior deception probability

3.  **Leverage integration:** We connect credibility to the DOF framework, showing credibility as a form of epistemic leverage

The theorems (Cheap Talk Bound, Magnitude Penalty, Meta-Assertion Trap) are new. The methodology is established.

## Objection 2: "Real communication isn't Bayesian"

**Objection:** "Humans don't update beliefs according to Bayes' rule. The rationality assumption is unrealistic."

**Response:** The rationality assumption provides *upper bounds*. If agents deviate from Bayesian reasoning, credibility bounds may be tighter (irrational skepticism) or looser (irrational credulity). The theorems characterize what is *achievable* under optimal reasoning---a ceiling, not a prediction.

For AI systems designed to be rational, the bounds are prescriptive. For human communication, they are normative benchmarks.

## Objection 3: "Costly signals aren't always truth-dependent"

**Objection:** "Expensive signals can be equally costly for liars and truth-tellers. Your distinction is too clean."

**Response:** Correct. The definition (Section 2) distinguishes:

-   **Truth-dependent costs:** Lying is more expensive than truth-telling (e.g., maintaining consistent false memories)

-   **Truth-independent costs:** Equal cost regardless of truth value (e.g., verbose phrasing)

Expensive signals with truth-independent costs remain cheap talk despite their expense. The credibility-enhancing property comes from the *differential*, not the absolute cost.

## Objection 4: "The magnitude penalty seems wrong"

**Objection:** "Detailed claims are often more credible, not less. The magnitude penalty contradicts intuition."

**Response:** The distinction is between:

-   **Detail about the claim:** Research, evidence, specificity---these are costly signals (effort-dependent) and credibility-enhancing

-   **Detail about credibility itself:** "I'm absolutely certain, trust me, this is verified"---these are cheap talk and subject to the magnitude penalty

The theorem applies to meta-assertions (claims about credibility), not to substantive claims. A detailed scientific argument is credibility-enhancing; a detailed assertion of trustworthiness is credibility-reducing.

## Objection 5: "The Lean proofs are trivial"

**Objection:** "The Lean proofs just formalize definitions. There's no deep mathematics."

**Response:** The value is precision, not difficulty. The proofs verify:

1.  The cheap talk bound follows from the cost-independence definition

2.  The magnitude penalty follows from the recursive structure of meta-assertions

3.  The impossibility results follow from the bound composition

Machine-checked proofs eliminate ambiguity in informal arguments. The contribution is verification, not complexity.

## Objection 6: "This doesn't apply to AI systems"

**Objection:** "AI systems can be designed to be trustworthy. The cheap talk bounds don't apply to engineered systems."

**Response:** The bounds apply to *communication about* trustworthiness, not to trustworthiness itself. An AI system can be trustworthy, but its *assertions* of trustworthiness are cheap talk unless backed by costly signals (audits, formal verification, track record).

The framework explains why "I am safe and helpful" is less credibility-enhancing than demonstrated safety and helpfulness.

## Objection 7: "The impossibility results are too strong"

**Objection:** "Theorem 5.1 says no string achieves high credibility for high-magnitude claims. But some claims are believed."

**Response:** The theorem applies to *cheap talk* strings. Credibility for high-magnitude claims requires costly signals:

-   Track record (historical accuracy)

-   Formal verification (mathematical proof)

-   Reputation stake (costly to lose)

-   Third-party attestation (independent verification)

The impossibility is for *verbal assertions alone*. Credibility is achievable through costly signals, not through phrasing.

## Objection 8: "The leverage integration is forced"

**Objection:** "Connecting credibility to DOF seems like a stretch. These are different concepts."

**Response:** The connection is structural. Credibility leverage is:

$$L_C = \frac{\Delta \text{Credibility}}{\text{Signal Cost}}$$

This parallels architectural leverage:

$$L = \frac{|\text{Capabilities}|}{\text{DOF}}$$

Both measure efficiency: capability per unit of constraint. The integration shows that credibility optimization follows the same mathematical structure as architectural optimization. This unification is the theoretical contribution.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper5_credibility/proofs/`
- Lines: 2057
- Theorems: 82
- `sorry` placeholders: 0
