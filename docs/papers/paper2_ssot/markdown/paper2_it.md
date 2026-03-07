# Paper: Exact Consistency in Interactive Multi-Location Encodings: Zero-Error Thresholds and Side Information Bounds

**Status**: IEEE Transactions on Information Theory-ready | **Lean**: 12818 lines, 583 theorems

---

## Abstract

_Abstract not available._

# Introduction

When a latent fact is represented at multiple locations and those representations may be modified over time, exact consistency becomes a zero-error information problem. An observer querying the system must either recover a unique authoritative value or confront an ambiguity class of mutually incompatible representations. This paper studies the information-theoretic structure of that problem.

Our starting point is an abstract multi-location encoding model. A fact $F$ is represented across locations $\{L_1,\dots,L_n\}$; some locations may be independent, while others may be derived from a common source. We ask two questions:

1.  What independent encoding rate guarantees exact consistency, i.e., zero probability of disagreement among reachable states?

2.  When disagreement exists, how much side information is necessary to resolve the ambiguity without error?

This places the problem in the orbit of zero-error and multi-terminal information theory [@shannon1956zero; @korner1973graphs; @lovasz1979shannon; @slepian1973noiseless]. The relevant object is not ordinary vanishing-error capacity, but an exact-consistency analogue of zero-error resolvability under repeated updates.

## Zero-Incoherence Capacity {#sec:encoding-problem}

We define the **zero-incoherence capacity** $C_0$ as the largest independent encoding rate achieving exactly zero disagreement among reachable states. In our model, rate is the number of independent encoding locations (degrees of freedom, DOF). The central characterization is:

::: center
:::

This is a zero-error style result in the Shannon tradition [@shannon1956zero; @korner1973graphs; @lovasz1979shannon], adapted to modifiable storage/encoding systems rather than one-shot channels.

**Main results.** Let DOF (Degrees of Freedom) denote the encoding rate: the number of independent locations that can hold distinct values simultaneously.

-   **Side Information (Theorem [\[thm:side-info\]](#thm:side-info){reference-type="ref" reference="thm:side-info"}):** exact resolution of a $k$-way ambiguity class requires $\geq \log_2 k$ bits (UNQ1).

-   **Achievability (Theorem [\[thm:capacity-achievability\]](#thm:capacity-achievability){reference-type="ref" reference="thm:capacity-achievability"}):** rate $1$ achieves zero incoherence (UNQ1).

-   **Converse (Theorem [\[thm:capacity-converse\]](#thm:capacity-converse){reference-type="ref" reference="thm:capacity-converse"}):** any higher independent rate fails to achieve zero incoherence (UNQ1).

-   **Capacity (Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}):** $C_0 = 1$ exactly (UNQ1).

::: theorem
For any incoherent encoding system and any resolution procedure, there exists a value present in the system that disagrees with the resolution. Without $\log_2 k$ bits of side information (where $k$ = DOF), no resolution is information-theoretically justified.
:::

This parallels zero-error decoding constraints [@korner1973graphs; @lovasz1979shannon]: without sufficient side information, exact reconstruction is impossible.

## Why This Is an Information-Theoretic Problem {#sec:optimal-rate}

The zero-incoherence threshold is stated in achievability/converse form:

::: center
  **Encoding Rate**    **Zero Incoherence?**   **Interpretation**
  ------------------- ----------------------- --------------------
  DOF $= 0$                     N/A             Fact not encoded
  DOF $= 1$                   **Yes**          Capacity-achieving
  DOF $> 1$                     No               Above capacity
:::

**Comparison to Shannon capacity.** Shannon's channel capacity $C$ is the supremum of rates $R$ achieving vanishing error probability: $\lim_{n \to \infty} P_e^{(n)} = 0$. Our zero-incoherence capacity is the supremum of rates achieving *exactly zero* incoherence probability, so the closest analogy is to zero-error capacity [@shannon1956zero], not ordinary capacity.

**Operational meaning.** The threshold identifies when ambiguity can be avoided entirely: one independent source can be propagated to many derived views without disagreement, while two or more independently writable sources create reachable ambiguity classes. The side-information theorem then quantifies the cost of resolving those classes once they exist.

## Applications Across Domains {#sec:applications}

The abstract encoding model applies wherever facts are stored redundantly:

-   **Distributed databases:** Replica consistency under partition constraints [@brewer2000cap]

-   **Version control:** Merge resolution when branches diverge [@hunt2002vcdiff]

-   **Configuration systems:** Multi-file settings with coherence requirements [@delaet2010survey]

-   **Software systems:** Class registries, type definitions, interface contracts [@hunt1999pragmatic]

In each domain, the question is identical: when do replicated representations permit a unique zero-error interpretation, and when do they require external side information for resolution? The software examples later in the paper are applications of this abstract question, not the primary object of study.

## Connection to Classical Information Theory {#sec:connection-it}

Our results extend classical source coding ideas to interactive multi-terminal systems whose stored representations are modified over time.

**1. Multi-terminal source coding.** Slepian-Wolf [@slepian1973noiseless] characterizes distributed encoding of correlated sources. We model encoding locations as terminals: derivation introduces *perfect correlation* (deterministic dependence), reducing effective rate. The capacity result shows that only complete correlation (all terminals derived from one source) guarantees coherence--partial correlation permits divergence. Section [\[sec:side-information\]](#sec:side-information){reference-type="ref" reference="sec:side-information"} develops this connection.

**2. Zero-error capacity.** Shannon [@shannon1956zero], Körner [@korner1973graphs], and Lovász [@lovasz1979shannon] characterize zero-error communication. We characterize **zero-incoherence encoding**--a storage analog where "errors" are disagreements among locations. The achievability/converse structure (Theorems [\[thm:capacity-achievability\]](#thm:capacity-achievability){reference-type="ref" reference="thm:capacity-achievability"}, [\[thm:capacity-converse\]](#thm:capacity-converse){reference-type="ref" reference="thm:capacity-converse"}) is intentionally cast in that style (UNQ1, UNQ1).

**3. Interactive information theory.** The BIRS workshop [@birs2012interactive] identified interactive IT as encoding/decoding with feedback and multi-round protocols. Our model is interactive: encodings are modified over time, and causal propagation (a realizability requirement) is analogous to channel feedback. Ma-Ishwar [@ma2011distributed] showed interaction can reduce rate; we show derivation (a form of interaction) can reduce effective DOF.

**4. Rate-complexity tradeoffs.** Rate-distortion theory [@cover2006elements] trades rate $R$ against distortion $D$. We trade encoding rate (DOF) against modification complexity $M$: DOF $= 1$ achieves $M = O(1)$; DOF $> 1$ requires $M = \Omega(n)$. The gap is unbounded (Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"}, UNQ1).

## Realizability and Applications {#sec:realizability}

A secondary question is which concrete systems can realize the capacity-achieving regime ($C_0 = 1$). We prove realizability requires two information-theoretic properties:

1.  **Causal update propagation (feedback coupling):** Changes to the source must automatically trigger updates to derived locations. This is analogous to *channel coding with feedback* [@cover2006elements]--the encoder (source) and decoder (derived locations) are coupled causally. Without feedback, a temporal window exists where source and derived locations diverge (temporary incoherence).

2.  **Provenance observability (decoder side information):** The system must support queries about derivation structure. This is the encoding-system analog of *Slepian-Wolf side information* [@slepian1973noiseless]--the decoder has access to structural information enabling verification that all terminals are derived from the source.

::: theorem
An encoding system achieves $C_0 = 1$ iff it provides both causal propagation and provenance observability (UNQ1). Neither alone suffices (Theorem [\[thm:independence\]](#thm:independence){reference-type="ref" reference="thm:independence"}, UNQ1).
:::

**Connection to multi-version coding.** Rashmi et al. [@rashmi2015multiversion] prove an "inevitable storage cost for consistency" in distributed storage. Our realizability theorem is analogous: systems lacking either encoder property *cannot* achieve capacity--the constraint is information-theoretic, not implementation-specific.

**Instantiations.** The encoder properties instantiate across domains: programming languages, distributed databases, and configuration systems. Section [\[sec:evaluation\]](#sec:evaluation){reference-type="ref" reference="sec:evaluation"} treats these only as corollaries of the abstract theory.

## Paper Organization {#overview}

Core theorems (capacity, realizability, complexity bounds) are machine-checked in Lean 4 [@demoura2021lean4] (12818 lines, 583 theorem/lemma statements, 0 `sorry` placeholders). The source proof tree now discharges the side-information/counting layer by finite zero-error arguments rather than paper-local assumption bundles.

**Section [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"}--Encoding Model and Capacity.** We define multi-location encoding systems, encoding rate (DOF), and coherence/incoherence. We introduce information-theoretic quantities (value entropy, redundancy, incoherence entropy). We prove the exact-consistency threshold ($C_0 = 1$) with explicit achievability/converse structure, and the side-information bound ($\geq \log_2 k$ bits for $k$-way resolution). We also record CAP/FLP-style analogues as secondary structural consequences of the model.

**Section [\[sec:ssot\]](#sec:ssot){reference-type="ref" reference="sec:ssot"}--Derivation and Optimal Rate.** We characterize derivation as the mechanism achieving capacity: derived locations are perfectly correlated with their source, contributing zero effective rate.

**Section [\[sec:requirements\]](#sec:requirements){reference-type="ref" reference="sec:requirements"}--Encoder Realizability.** We prove that realizing the threshold in concrete systems requires causal propagation (feedback) and provenance observability (decoder side information). Both are necessary; together sufficient.

**Section [\[sec:bounds\]](#sec:bounds){reference-type="ref" reference="sec:bounds"}--Rate-Complexity Tradeoffs.** We prove modification complexity is $O(1)$ at capacity vs. $\Omega(n)$ above capacity. The gap is unbounded.

**Sections [\[sec:evaluation\]](#sec:evaluation){reference-type="ref" reference="sec:evaluation"}, [\[sec:empirical\]](#sec:empirical){reference-type="ref" reference="sec:empirical"}--Applications (Corollaries).** A language-level instantiation and a brief worked example. These illustrate the abstract theory; core results are domain-independent.

## Core Theorems {#sec:core-theorems}

We establish five *core* theorem families, with the side-information bound serving as the main quantitative IT statement:

1.  **Theorem [\[thm:side-info\]](#thm:side-info){reference-type="ref" reference="thm:side-info"} (Side Information Bound):** Resolution of a $k$-way ambiguity class requires $\geq \log_2 k$ bits of side information. At DOF $= 1$, zero bits suffice (UNQ1).

    *Proof:* The $k$ alternatives require at least $k$ distinguishable side-information tags, hence at least $\log_2 k$ bits.

2.  **Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"} (Zero-Incoherence Capacity):** $C_0 = 1$. The maximum encoding rate guaranteeing zero incoherence is exactly 1 (UNQ1).

    *Structure:* Achievability (Theorem [\[thm:capacity-achievability\]](#thm:capacity-achievability){reference-type="ref" reference="thm:capacity-achievability"}) + Converse (Theorem [\[thm:capacity-converse\]](#thm:capacity-converse){reference-type="ref" reference="thm:capacity-converse"}).

3.  **Theorem [\[thm:oracle-arbitrary\]](#thm:oracle-arbitrary){reference-type="ref" reference="thm:oracle-arbitrary"} (Resolution Impossibility):** Without side information, no resolution procedure is information-theoretically justified (UNQ1).

    *Proof:* By incoherence, $k \geq 2$ values exist. Any selection leaves $k-1$ values disagreeing. No internal information distinguishes them.

4.  **Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"} (Encoder Realizability):** Achieving capacity requires encoder properties: (a) causal propagation (feedback), and (b) provenance observability (side information). Both necessary; together sufficient (UNQ1).

    *Proof:* Necessity by constructing above-capacity configurations when either is missing. Sufficiency by exhibiting capacity-achieving encoders.

5.  **Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"} (Rate-Complexity Tradeoff):** Modification complexity scales as $O(1)$ at capacity vs. $\Omega(n)$ above capacity. The gap is unbounded (UNQ1).

    *Proof:* At capacity, one source update suffices. Above capacity, $n$ independent locations require $n$ updates.

**Uniqueness.** $C_0 = 1$ is the unique exact-consistency rate in the model: DOF $= 0$ fails to encode, while DOF $> 1$ exceeds the zero-incoherence regime (UNQ1, UNQ1).

## Scope {#sec:scope}

The abstract model covers facts represented at multiple locations under allowed edits. The concrete realizability results in this paper focus on *structural facts* (class existence, method signatures, type relationships), because these provide the clearest exact-consistency setting. The complexity analysis is asymptotic in the number of encoding locations.

**Cross-system realizations.** Multi-language or cross-runtime realizations typically require external code generation or synchronization layers. Those are natural applications of the model, but their detailed treatment is left for future work (Section [\[sec:conclusion\]](#sec:conclusion){reference-type="ref" reference="sec:conclusion"}).

## Contributions {#sec:contributions}

This paper makes four primary information-theoretic contributions and one secondary structural observation:

**1. Exact-consistency threshold (Section [\[sec:capacity\]](#sec:capacity){reference-type="ref" reference="sec:capacity"}):**

-   Definition of encoding rate (DOF), coherence, and ambiguity

-   **Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}:** $C_0 = 1$ (tight: achievability + converse) (UNQ1, UNQ1, UNQ1)

-   **Theorem [\[thm:redundancy-incoherence\]](#thm:redundancy-incoherence){reference-type="ref" reference="thm:redundancy-incoherence"}:** Redundancy $\rho > 0$ iff incoherence reachable (UNQ1)

**2. Side information bounds (Section [\[sec:side-information\]](#sec:side-information){reference-type="ref" reference="sec:side-information"}):**

-   **Theorem [\[thm:side-info\]](#thm:side-info){reference-type="ref" reference="thm:side-info"}:** $k$-way resolution requires $\geq \log_2 k$ bits (UNQ1)

-   **Corollary [\[cor:dof1-zero-side\]](#cor:dof1-zero-side){reference-type="ref" reference="cor:dof1-zero-side"}:** DOF $= 1$ requires zero side information (UNQ1)

-   Multi-terminal interpretation: derivation as perfect dependence

**3. Encoder realizability (Section [\[sec:requirements\]](#sec:requirements){reference-type="ref" reference="sec:requirements"}):**

-   **Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}:** Capacity achieved iff causal propagation AND provenance observability (UNQ1)

-   **Theorem [\[thm:independence\]](#thm:independence){reference-type="ref" reference="thm:independence"}:** Requirements are independent (UNQ1, UNQ1)

-   Connection to feedback and side-information models

**4. Rate-complexity tradeoffs (Section [\[sec:bounds\]](#sec:bounds){reference-type="ref" reference="sec:bounds"}):**

-   **Theorem [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"}:** $O(1)$ at capacity (UNQ1)

-   **Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"}:** $\Omega(n)$ above capacity (UNQ1)

-   **Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"}:** Gap unbounded (UNQ1)

**5. Structural analogies to CAP/FLP (Section [\[sec:cap-flp\]](#sec:cap-flp){reference-type="ref" reference="sec:cap-flp"}):**

-   **Theorem [\[thm:cap-encoding\]](#thm:cap-encoding){reference-type="ref" reference="thm:cap-encoding"}:** CAP-style impossibility in the encoding model (UNQ1)

-   **Theorem [\[thm:static-flp\]](#thm:static-flp){reference-type="ref" reference="thm:static-flp"}:** FLP-style resolution impossibility in incoherent states (UNQ1)

**Applications (corollaries).** Sections [\[sec:evaluation\]](#sec:evaluation){reference-type="ref" reference="sec:evaluation"} and [\[sec:empirical\]](#sec:empirical){reference-type="ref" reference="sec:empirical"} instantiate the realizability theorem in language-level terms and provide a worked example. These are illustrative corollaries; the core information-theoretic results are self-contained in Sections [\[sec:foundations\]](#sec:foundations){reference-type="ref" reference="sec:foundations"}--[\[sec:bounds\]](#sec:bounds){reference-type="ref" reference="sec:bounds"}.


# Encoding Systems and Coherence {#sec:foundations}

We formalize exact consistency for multi-location encodings with modification constraints. The goal of this section is to isolate the abstract IT model before any software-specific interpretation: facts take values in finite alphabets, system states expose multiple representations of those facts, edits move the system among reachable states, and the observer must determine whether the represented fact is uniquely recoverable.

## Model assumptions and notation {#sec:assumptions}

For rigour we state the modeling assumptions used throughout the paper. These are intentionally minimal and are made explicit so reviewers can judge applicability.

1.  **Fact value model (A1):** Each fact $F$ takes values in a finite set $\mathcal{V}_F$; $H(F)=\log_2|\mathcal{V}_F|$ denotes its entropy under a chosen prior. When we write "zero probability of incoherence" we mean $\Pr(\text{incoherent})=0$ under the model for edits and randomness specified below.

2.  **Update model (A2):** Modifications occur as discrete events (rounds). An edit $\delta_F$ changes the source value for $F$; derived locations update deterministically when causal propagation is present. We do not require a blocklength parameter; our asymptotic statements are in the number of encoding locations $n$ or in ensemble scaling of the codebase.

3.  **Adversary / randomness (A3):** When randomness is needed we assume a benign stochastic model for edits (e.g., uniformly sampled new values for illustration). For impossibility/converse statements we make no cooperative assumptions of the editor: adversarial sequences of edits that produce incoherence are allowed when DOF $>1$.

4.  **Side-information channel (A4):** Derived locations and runtime queries collectively form side information $S$ available to any verifier. In the finite zero-error layer, the relevant quantity is the number of distinguishable tags that $S$ can expose.

References to these assumptions use labels (A1)--(A4). Full formal versions of the operational model are given in the mechanized supplement (Supplement A).

## The Encoding Model {#sec:epistemic}

We begin with the abstract encoding model: locations, values, reachable states, and ambiguity.

::: definition
[]{#def:encoding-system label="def:encoding-system"} An *encoding system* for a fact $F$ is a collection of locations $\{L_1, \ldots, L_n\}$, each capable of holding a value for $F$.
:::

::: definition
[]{#def:coherence label="def:coherence"} An encoding system is *coherent* iff all locations hold the same value: $$\forall i, j: \text{value}(L_i) = \text{value}(L_j)$$
:::

::: definition
[]{#def:incoherence label="def:incoherence"} An encoding system is *incoherent* iff some locations disagree: $$\exists i, j: \text{value}(L_i) \neq \text{value}(L_j)$$
:::

::: definition
[]{#def:ambiguity-class label="def:ambiguity-class"} For a system state $x$, the *ambiguity class* of $x$ is the set $$\mathcal A(x) = \{v : \exists L \text{ with } \text{value}(L)=v\}.$$ When $|\mathcal A(x)|>1$, the state presents multiple internally supported candidate values for the same fact.
:::

**The zero-error resolution problem.** Given a state $x$, a resolver must output the correct value of $F$ with zero error. When $|\mathcal A(x)|>1$, the internal state alone may fail to identify a unique answer.

::: theorem
[]{#thm:oracle-arbitrary label="thm:oracle-arbitrary"} For any incoherent encoding system state $x$ and any oracle $O$ that resolves $x$ to a value $v \in \mathcal A(x)$, there exists a value $v' \in \mathcal A(x)$ such that $v' \neq v$.
:::

::: proof
*Proof.* By incoherence, $|\mathcal A(x)|>1$, so there exist $v_1,v_2\in\mathcal A(x)$ with $v_1\neq v_2$. Either $O$ picks $v_1$ (then $v_2$ disagrees) or it does not pick $v_1$ (then $v_1$ disagrees). ◻
:::

**Interpretation.** This is the first zero-error obstruction in the paper: once an ambiguity class contains more than one value, the state itself does not identify which value is authoritative. Any exact resolver must therefore use auxiliary information not contained in the state representation alone.

::: definition
[]{#def:dof-epistemic label="def:dof-epistemic"} The *degrees of freedom* (DOF) of an encoding system is the number of locations that can be modified independently.
:::

::: theorem
[]{#thm:dof-one-coherence label="thm:dof-one-coherence"} If DOF = 1, then the encoding system is coherent in all reachable states.
:::

::: proof
*Proof.* With DOF = 1, exactly one location is independent. All other locations are derived (automatically updated when the source changes). Derived locations cannot diverge from their source. Therefore, all locations hold the value determined by the single independent source. Disagreement is impossible. ◻
:::

::: theorem
[]{#thm:dof-gt-one-incoherence label="thm:dof-gt-one-incoherence"} If DOF $> 1$, then incoherent states are reachable.
:::

::: proof
*Proof.* With DOF $> 1$, at least two locations are independent. Independent locations can be modified separately. A sequence of edits can set $L_1 = v_1$ and $L_2 = v_2$ where $v_1 \neq v_2$. This is an incoherent state. ◻
:::

::: corollary
[]{#cor:coherence-forces-ssot label="cor:coherence-forces-ssot"} If coherence must be guaranteed (no incoherent states reachable), then DOF = 1 is necessary and sufficient.
:::

This is the basic exact-consistency criterion in the model (UNQ1, UNQ1, UNQ1).

The following subsections refine this model and then connect it back to concrete systems only as examples.

## Computational Realizations {#sec:edit-space}

The abstract encoding model (Definitions [\[def:encoding-system\]](#def:encoding-system){reference-type="ref" reference="def:encoding-system"}--[\[def:dof-epistemic\]](#def:dof-epistemic){reference-type="ref" reference="def:dof-epistemic"}) applies to any system where:

1.  Facts are encoded at multiple locations

2.  Locations can be modified

3.  Correctness requires coherence across modifications

**Domains satisfying these constraints:**

-   **Software codebases:** Type definitions, registries, configurations

-   **Distributed databases:** Replica consistency under updates

-   **Configuration systems:** Multi-file settings (e.g., infrastructure-as-code)

-   **Version control:** Merge resolution under concurrent modifications

We focus on *computational realizations* only to anchor the model. Software codebases are a convenient example, but the theorems in this section are stated independently of any language, runtime, or toolchain.

::: definition
A *codebase* $C$ is a finite collection of source files, each containing syntactic constructs (classes, functions, statements, expressions). This is the canonical computational encoding system.
:::

::: definition
A *location* $L \in C$ is a syntactically identifiable region: a class definition, function body, configuration value, type annotation, database field, or configuration entry.
:::

::: definition
For encoding system $C$, the *modification space* $E(C)$ is the set of all valid modifications. Each edit $\delta \in E(C)$ transforms $C$ into $C' = \delta(C)$.
:::

The modification space is large (exponential in system size). But we focus on modifications that *change a specific fact*.

## Facts: Atomic Units of Specification {#sec:facts}

::: definition
[]{#def:fact label="def:fact"} A *fact* $F$ is an atomic unit of program specification: a single piece of knowledge that can be independently modified. Facts are the indivisible units of meaning in a specification.
:::

The granularity of facts is determined by the specification, not the implementation. If two pieces of information must always change together, they constitute a single fact. If they can change independently, they are separate facts.

**Examples of facts:**

::: center
  **Fact**                                           **Description**
  -------------------------------------------------- -----------------------------
  $F_1$: "threshold = 0.5"                           A configuration value
  $F_2$: "`PNGLoader` handles `.png`"                A type-to-handler mapping
  $F_3$: "`validate()` returns `bool`"               A method signature
  $F_4$: "`Detector` is a subclass of `Processor`"   An inheritance relationship
  $F_5$: "`Config` has field `name: str`"            A dataclass field
:::

::: definition
[]{#def:structural-fact label="def:structural-fact"} A fact $F$ is *structural* with respect to encoding system $C$ iff the locations encoding $F$ are fixed at definition time: $$\begin{aligned}
\text{structural}(F, C) \Longleftrightarrow\;
&\forall L:\; \text{encodes}(L, F) \\
&\rightarrow\; L \in \text{DefinitionSyntax}(C)
\end{aligned}$$ where $\text{DefinitionSyntax}(C)$ comprises declarative constructs that cannot change post-definition without recreation.
:::

**Examples across domains:**

-   **Software:** Class declarations, method signatures, inheritance clauses, attribute definitions

-   **Databases:** Schema definitions, table structures, foreign key constraints

-   **Configuration:** Infrastructure topology, service dependencies

-   **Version control:** Branch structure, merge policies

**Key property:** Structural facts are fixed at *definition time*. Once defined, their structure cannot change without recreation. This is why structural coherence requires definition-time computation: the encoding locations are only mutable during creation.

**Non-structural facts** (runtime values, mutable state) have encoding locations modifiable post-definition. Achieving DOF = 1 for non-structural facts requires different mechanisms (reactive bindings, event systems) and is outside this paper's scope. We focus on structural facts because they demonstrate the impossibility results most clearly.

## Encoding: The Correctness Relationship {#sec:encoding}

::: definition
[]{#def:encodes label="def:encodes"} Location $L$ *encodes* fact $F$, written $\text{encodes}(L, F)$, iff correctness requires updating $L$ when $F$ changes.

Formally: $$\text{encodes}(L, F) \Longleftrightarrow \forall \delta_F: \neg\text{updated}(L, \delta_F) \rightarrow \text{incorrect}(\delta_F(C))$$

where $\delta_F$ is an edit targeting fact $F$.
:::

**Key insight:** This definition is induced by correctness rather than by annotation. If failing to update location $L$ when fact $F$ changes produces an incorrect system, then $L$ participates in the representation of $F$.

:::: example
[]{#ex:encoding label="ex:encoding"} Consider a type registry:

::: code
\# Location L1: Class definition class PNGLoader(ImageLoader): format = \"png\"

\# Location L2: Registry entry LOADERS = \"png\": PNGLoader, \"jpg\": JPGLoader

\# Location L3: Documentation \# Supported formats: png, jpg
:::

The fact $F$ = "`PNGLoader` handles `png`" is encoded at:

-   $L_1$: The class definition (primary encoding)

-   $L_2$: The registry dictionary (secondary encoding)

-   $L_3$: The documentation comment (tertiary encoding)

If $F$ changes (e.g., to "`PNGLoader` handles `png` and `apng`"), all three locations must be updated for correctness. The program is incorrect if $L_2$ still says `{"png": PNGLoader}` when the class now handles both formats.
::::

## Modification Complexity {#sec:mod-complexity}

::: definition
[]{#def:mod-complexity label="def:mod-complexity"} $$M(C, \delta_F) = |\{L \in C : \text{encodes}(L, F)\}|$$ The number of locations that must be updated when fact $F$ changes.
:::

Modification complexity is the central metric of this paper. It measures the *cost* of changing a fact. A codebase with $M(C, \delta_F) = 47$ requires 47 edits to correctly implement a change to fact $F$. A codebase with $M(C, \delta_F) = 1$ requires only 1 edit.

::: theorem
[]{#thm:correctness-forcing label="thm:correctness-forcing"} $M(C, \delta_F)$ is the **minimum** number of edits required for correctness. Fewer edits imply an incorrect program.
:::

::: proof
*Proof.* Suppose $M(C, \delta_F) = k$, meaning $k$ locations encode $F$. By Definition [\[def:encodes\]](#def:encodes){reference-type="ref" reference="def:encodes"}, each encoding location must be updated when $F$ changes. If only $j < k$ locations are updated, then $k - j$ locations still reflect the old value of $F$. These locations create inconsistencies:

1.  The specification says $F$ has value $v'$ (new)

2.  Locations $L_1, \ldots, L_j$ reflect $v'$

3.  Locations $L_{j+1}, \ldots, L_k$ reflect $v$ (old)

By Definition [\[def:encodes\]](#def:encodes){reference-type="ref" reference="def:encodes"}, the program is incorrect. Therefore, all $k$ locations must be updated, and $k$ is the minimum. ◻
:::

## Independence and Degrees of Freedom {#sec:dof}

Not all encoding locations are created equal. Some are *derived* from others.

::: definition
[]{#def:independent label="def:independent"} Locations $L_1, L_2$ are *independent* for fact $F$ iff they can diverge. Updating $L_1$ does not automatically update $L_2$, and vice versa.

Formally: $L_1$ and $L_2$ are independent iff there exists a sequence of edits that makes $L_1$ and $L_2$ encode different values for $F$.
:::

::: definition
[]{#def:derived label="def:derived"} Location $L_{\text{derived}}$ is *derived from* $L_{\text{source}}$ iff updating $L_{\text{source}}$ automatically updates $L_{\text{derived}}$. Derived locations are not independent of their sources.
:::

::::: example
[]{#ex:independence label="ex:independence"} Consider two architectures for the type registry:

**Architecture A (independent locations):**

::: code
\# L1: Class definition class PNGLoader(ImageLoader): \...

\# L2: Manual registry (independent of L1) LOADERS = \"png\": PNGLoader
:::

Here $L_1$ and $L_2$ are independent. A developer can change $L_1$ without updating $L_2$, causing inconsistency.

**Architecture B (derived location):**

::: code
\# L1: Class definition with registration class PNGLoader(ImageLoader): format = \"png\"

\# L2: Derived registry (computed from L1) LOADERS = cls.format: cls for cls in ImageLoader.\_\_subclasses\_\_()
:::

Here $L_2$ is derived from $L_1$. Updating the class definition automatically updates the registry. They cannot diverge.
:::::

::: definition
[]{#def:dof label="def:dof"} $$\text{DOF}(C, F) = |\{L \in C : \text{encodes}(L, F) \land \text{independent}(L)\}|$$ The number of *independent* locations encoding fact $F$.
:::

DOF is the key metric. Modification complexity $M$ counts all encoding locations. DOF counts only the independent ones. If all but one encoding location is derived, DOF = 1 even though $M$ can be large.

::: theorem
[]{#thm:dof-inconsistency label="thm:dof-inconsistency"} $\text{DOF}(C, F) = k$ implies that up to $k$ distinct values for $F$ can coexist simultaneously. In particular, $k>1$ makes ambiguity reachable.
:::

::: proof
*Proof.* Each independent location can hold a different value. By Definition [\[def:independent\]](#def:independent){reference-type="ref" reference="def:independent"}, no constraint forces agreement between independent locations. Therefore, $k$ independent locations can simultaneously realize up to $k$ distinct values. ◻
:::

::: corollary
[]{#cor:dof-risk label="cor:dof-risk"} $\text{DOF}(C, F) > 1$ implies incoherent states are reachable.
:::

## The DOF Lattice {#sec:dof-lattice}

DOF values partition the model into three regimes:

::: center
   **DOF**  **Encoding Status**
  --------- ----------------------------------------------------------------
      0     Fact $F$ is not encoded (no representation)
      1     Coherence guaranteed (optimal rate under coherence constraint)
   $k > 1$  Incoherence possible (redundant independent encodings)
:::

::: theorem
[]{#thm:dof-optimal label="thm:dof-optimal"} For any fact $F$ that must be encoded, $\text{DOF}(C, F) = 1$ is the unique value guaranteeing coherence:

1.  DOF = 0: Fact is not represented

2.  DOF = 1: Coherence guaranteed (by Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"})

3.  DOF $>$ 1: Incoherence reachable (by Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"})

This theorem is deliberately simple: it records the exact-consistency trichotomy of the model before the later side-information and complexity consequences are added. The same trichotomy is recast as a capacity statement in Section [1.11](#sec:capacity){reference-type="ref" reference="sec:capacity"}.
:::

## Encoding-Theoretic CAP and FLP {#sec:cap-flp}

We record two structural analogies to CAP and FLP inside the encoding model (UNQ1, UNQ1). These are secondary to the main IT contribution.

::: definition
[]{#def:local-availability label="def:local-availability"} An encoding system for fact $F$ is *locally available* iff for every encoding location $L$ of $F$ and every value $v$, there exists a valid edit $\delta \in E(C)$ such that $\text{updated}(L, \delta)$ and for every other encoding location $L'$, $\neg \text{updated}(L', \delta)$. Informally: each encoding location can be updated without coordinating with others.
:::

::: definition
[]{#def:partition-tolerance label="def:partition-tolerance"} An encoding system for fact $F$ is *partition-tolerant* iff $F$ is encoded at two or more locations: $$|\{L \in C : \text{encodes}(L, F)\}| \ge 2.$$ This is the minimal formal notion of "replication" in our model; without it, partitions are vacuous.
:::

::: theorem
[]{#thm:cap-encoding label="thm:cap-encoding"} No encoding system can simultaneously guarantee coherence (Definition [\[def:coherence\]](#def:coherence){reference-type="ref" reference="def:coherence"}), local availability (Definition [\[def:local-availability\]](#def:local-availability){reference-type="ref" reference="def:local-availability"}), and partition tolerance (Definition [\[def:partition-tolerance\]](#def:partition-tolerance){reference-type="ref" reference="def:partition-tolerance"}) for the same fact $F$.
:::

::: proof
*Proof.* Partition tolerance gives at least two encoding locations. Local availability allows each to be updated without updating any other encoding location, so by Definition [\[def:independent\]](#def:independent){reference-type="ref" reference="def:independent"} there exist two independent locations and thus $\text{DOF}(C, F) > 1$. By Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"}, incoherent states are reachable, contradicting coherence. ◻
:::

::: definition
[]{#def:resolution-procedure label="def:resolution-procedure"} A *resolution procedure* is a deterministic function $R$ that maps an encoding system state to a value present in that state.
:::

::: theorem
[]{#thm:static-flp label="thm:static-flp"} For any incoherent encoding system state and any resolution procedure $R$, the returned value is arbitrary relative to the other values present; no deterministic $R$ can be justified by internal information alone.
:::

::: proof
*Proof.* Immediate from Theorem [\[thm:oracle-arbitrary\]](#thm:oracle-arbitrary){reference-type="ref" reference="thm:oracle-arbitrary"}: in an incoherent state, at least two distinct values are present, and any choice leaves another value disagreeing. ◻
:::

These theorems are the encoding-theoretic counterparts of CAP [@brewer2000cap; @gilbert2002cap] and FLP [@flp1985impossibility]: CAP corresponds to the impossibility of coherence when replicated encodings remain independently updatable; FLP corresponds to the impossibility of truth-preserving resolution in an incoherent state without side information.

## Information-Theoretic Quantities {#sec:it-quantities}

Before establishing the main threshold result, we define the information-theoretic quantities used to express ambiguity, redundancy, and side-information requirements.

::: definition
[]{#def:encoding-rate label="def:encoding-rate"} The *encoding rate* of system $C$ for fact $F$ is $R(C, F) = \text{DOF}(C, F)$, the number of independent encoding locations. This counts locations that can hold distinct values simultaneously.
:::

::: definition
[]{#def:value-entropy label="def:value-entropy"} For a fact $F$ with value space $\mathcal{V}_F$, the *value entropy* is: $$H(F) = \log_2 |\mathcal{V}_F|$$ This is the information content of specifying $F$'s value.
:::

::: definition
[]{#def:redundancy label="def:redundancy"} The *encoding redundancy* of system $C$ for fact $F$ is: $$\rho(C, F) = \text{DOF}(C, F) - 1$$ Redundancy measures excess independent encodings beyond the minimum needed to represent $F$.
:::

::: theorem
[]{#thm:redundancy-incoherence label="thm:redundancy-incoherence"} Encoding redundancy $\rho > 0$ is necessary and sufficient for incoherence reachability: $$\rho(C, F) > 0 \Longleftrightarrow \text{incoherent states reachable}$$
:::

::: proof
*Proof.* $(\Rightarrow)$ If $\rho > 0$, then DOF $> 1$. By Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"}, incoherent states are reachable.

$(\Leftarrow)$ If incoherent states are reachable, then by contrapositive of Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"}, DOF $\neq 1$. Since the fact is encoded, DOF $\geq 1$, so DOF $> 1$, hence $\rho > 0$. ◻
:::

::: definition
[]{#def:incoherence-entropy label="def:incoherence-entropy"} For a state whose ambiguity class has size $k$, the *incoherence entropy* is: $$H_{\text{inc}} = \log_2 k$$ This quantifies the uncertainty about which value is authoritative.
:::

## Zero-Incoherence Capacity Theorem {#sec:capacity}

We now establish the central exact-consistency characterization. The argument is elementary at the combinatorial level, but it serves as the base layer for the later side-information and rate-complexity consequences. In that sense the section plays the role that an achievability/converse theorem plays in classical IT.

**Background: Zero-Error Capacity.** Shannon [@shannon1956zero] introduced zero-error capacity: the maximum rate at which information can be transmitted with *zero* probability of error. Körner [@korner1973graphs] and Lovász [@lovasz1979shannon] linked such questions to confusability structure. Our zero-incoherence capacity is the corresponding exact-consistency threshold for modifiable encodings.

::: definition
[]{#def:coherence-capacity label="def:coherence-capacity"} The *zero-incoherence capacity* of an encoding system is: $$C_0 = \sup\{R : \text{encoding rate } R \Rightarrow \text{incoherence probability} = 0\}$$ where "incoherence probability = 0" means no incoherent state is reachable under any modification sequence.
:::

::: theorem
[]{#thm:coherence-capacity label="thm:coherence-capacity"} The zero-incoherence capacity of any encoding system under independent modification is exactly 1: $$C_0 = 1$$
:::

We state the result in achievability/converse form because later sections attach nontrivial side-information and complexity consequences to the same threshold.

::: theorem
[]{#thm:capacity-achievability label="thm:capacity-achievability"} Encoding rate DOF $= 1$ achieves zero incoherence. Therefore $C_0 \geq 1$.
:::

::: proof
*Proof.* Let DOF$(C, F) = 1$. By Definition [\[def:dof\]](#def:dof){reference-type="ref" reference="def:dof"}, exactly one location $L_s$ is independent; all other locations $\{L_i\}$ are derived from $L_s$.

By Definition [\[def:derived\]](#def:derived){reference-type="ref" reference="def:derived"}, derived locations satisfy: $\text{update}(L_s) \Rightarrow \text{automatically\_updated}(L_i)$. Therefore, for any reachable state: $$\forall i: \text{value}(L_i) = f_i(\text{value}(L_s))$$ where $f_i$ is the derivation function. All values are determined by $L_s$. Disagreement requires two locations with different determining sources, but only $L_s$ exists. Therefore, no incoherent state is reachable. ◻
:::

::: theorem
[]{#thm:capacity-converse label="thm:capacity-converse"} Encoding rate DOF $> 1$ does not achieve zero incoherence. Therefore $C_0 < R$ for all $R > 1$.
:::

::: proof
*Proof.* Let DOF$(C, F) = k > 1$. By Definition [\[def:independent\]](#def:independent){reference-type="ref" reference="def:independent"}, there exist locations $L_1, L_2$ that can be modified independently.

**Construction of incoherent state:** Consider the modification sequence:

1.  $\delta_1$: Set $L_1 = v_1$ for some $v_1 \in \mathcal{V}_F$

2.  $\delta_2$: Set $L_2 = v_2$ for some $v_2 \neq v_1$

Both modifications are valid (each location accepts values from $\mathcal{V}_F$). By independence, $\delta_2$ does not affect $L_1$. The resulting state has: $$\text{value}(L_1) = v_1 \neq v_2 = \text{value}(L_2)$$

By Definition [\[def:incoherence\]](#def:incoherence){reference-type="ref" reference="def:incoherence"}, this state is incoherent. Since it is reachable, zero incoherence is not achieved.

The converse is intentionally combinatorial: once two independently writable locations exist, one can construct a reachable disagreement state. Later sections refine the same obstruction using finite zero-error side-information counting arguments. ◻
:::

::: proof
*Proof of Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}.* By Theorem [\[thm:capacity-achievability\]](#thm:capacity-achievability){reference-type="ref" reference="thm:capacity-achievability"}, $C_0 \geq 1$.

By Theorem [\[thm:capacity-converse\]](#thm:capacity-converse){reference-type="ref" reference="thm:capacity-converse"}, $C_0 < R$ for all $R > 1$.

Therefore $C_0 = 1$ exactly. The bound is tight: achieved at DOF $= 1$, not achieved at any DOF $> 1$. ◻
:::

**Comparison to Shannon capacity.** The analogy to channel coding is structural rather than literal:

:::: center
::: tabularx
@\>p0.19YY@ **Aspect** & **Shannon (Channel)** & **This Work (Encoding)**\
Rate & Bits per channel use & Independent encoding locations\
Constraint & Error probability $\to 0$ & Incoherence probability $= 0$\
Achievability & $R < C$ achieves & DOF $= 1$ achieves\
Converse & $R > C$ fails & DOF $> 1$ fails\
Capacity & $C = \max I(X;Y)$ & $C_0 = 1$\
:::
::::

The key difference is that Shannon capacity concerns communication over noisy channels, while the present threshold concerns exact consistency of stored representations under allowed edits.

::: corollary
[]{#cor:capacity-unique label="cor:capacity-unique"} DOF $= 1$ is the unique capacity-achieving encoding rate. No alternative achieves zero incoherence at higher rate.
:::

::: corollary
[]{#cor:redundancy-above label="cor:redundancy-above"} Any encoding with $\rho > 0$ (redundancy) operates above capacity and cannot guarantee coherence.
:::

### Zero-Distortion Boundary

The model induces a degenerate zero-distortion boundary: the only rate achieving perfect coherence is rate $1$.

::: definition
[]{#def:rate-incoherence label="def:rate-incoherence"} For $\epsilon\in[0,1]$, define $$R(\epsilon) = \inf\{R : \exists \text{ encoding achieving } P(\text{incoherence}) \leq \epsilon\}$$ where $\epsilon \in [0, 1]$ is the tolerable incoherence probability.
:::

::: theorem
[]{#thm:rate-incoherence-step label="thm:rate-incoherence-step"} At the zero-error point, the minimum achievable rate is exactly one: $$R(0)=1.$$ For every $\epsilon>0$, the model imposes no nontrivial upper bound on admissible independent rate.
:::

::: proof
*Proof.* The zero-error statement is exactly Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}. Once a positive incoherence budget is allowed, the model no longer forbids higher independent rate, so no analogous finite cutoff remains. ◻
:::

**Interpretation.** Unlike classical rate-distortion curves, the interesting point here is the sharp zero-error boundary: perfect coherence isolates a single admissible rate.

### Design Necessity

The threshold result also yields a simple design corollary:

::: theorem
[]{#thm:design-necessity label="thm:design-necessity"} If an encoding system requires zero incoherence for correctness, then the encoding rate must satisfy DOF $\leq 1$. This is a necessary condition; no design choice can circumvent it.
:::

::: proof
*Proof.* Suppose a system requires $P(\text{incoherence}) = 0$ and has DOF $> 1$. By Theorem [\[thm:capacity-converse\]](#thm:capacity-converse){reference-type="ref" reference="thm:capacity-converse"}, incoherent states are reachable. This contradicts the requirement. Therefore DOF $\leq 1$ is necessary.

The bound is not an implementation artifact: with DOF $> 1$, independent locations can diverge by construction. ◻
:::

::: corollary
[]{#cor:architectural-forcing label="cor:architectural-forcing"} For any fact $F$ requiring coherence guarantees, system architecture must either:

1.  Achieve DOF$(F) = 1$ through derivation mechanisms, or

2.  Accept that coherence cannot be guaranteed and implement resolution protocols with $\geq \log_2(\text{DOF})$ bits of side information.

There is no third option.
:::

### Coding Interpretation of Derivation

The coding-theoretic interpretation is compact: derivation is the capacity-achieving dependence structure. One location carries the independent value and the remaining locations are deterministic views. Those views improve observability without increasing independent rate.

### Connection to Confusability Graphs

Körner [@korner1973graphs] and Lovász [@lovasz1979shannon] characterized zero-error capacity via *confusability graphs*: vertices are channel inputs, edges connect inputs that can produce the same output. Zero-error capacity is determined by the graph's independence number.

We can define an analogous *incoherence graph* for encoding systems:

::: definition
[]{#def:incoherence-graph label="def:incoherence-graph"} For encoding system $C$ and fact $F$, the incoherence graph $G = (V, E)$ has:

-   Vertices $V =$ independent encoding locations

-   Edge $(L_i, L_j) \in E$ iff $L_i$ and $L_j$ can hold different values (are truly independent)
:::

::: theorem
[]{#thm:incoherence-graph label="thm:incoherence-graph"} Zero incoherence is achievable iff the incoherence graph has at most one vertex: $|V| \leq 1$.
:::

::: proof
*Proof.* If $|V| = 0$, no locations encode $F$. If $|V| = 1$, DOF $= 1$ and zero incoherence is achieved by Theorem [\[thm:capacity-achievability\]](#thm:capacity-achievability){reference-type="ref" reference="thm:capacity-achievability"}. If $|V| \geq 2$, DOF $\geq 2$ and incoherence is reachable by Theorem [\[thm:capacity-converse\]](#thm:capacity-converse){reference-type="ref" reference="thm:capacity-converse"}. ◻
:::

This graph view is intentionally simple. Its value is not a deep graph invariant, but a compact bridge to zero-error language before the richer confusability bounds used later.

## Side Information for Resolution {#sec:side-information}

When an encoding system is incoherent, exact resolution requires external side information. This is the point where the paper becomes genuinely information-theoretic: ambiguity size induces a quantitative lower bound on the information a resolver must obtain.

### The Multi-Terminal View

We can view an encoding system as a *multi-terminal source coding* problem [@slepian1973noiseless; @cover2006elements]:

-   Each encoding location is a *terminal* that can transmit (store) a value

-   The fact $F$ is the *source* to be encoded

-   *Derivation* introduces correlation: a derived terminal's output is a deterministic function of its source terminal

-   The *decoder* (any observer querying the system) must reconstruct $F$'s value

In Slepian-Wolf coding, correlated sources $(X, Y)$ can be encoded at rates $(R_X, R_Y)$ satisfying $R_X \geq H(X|Y)$, $R_Y \geq H(Y|X)$, $R_X + R_Y \geq H(X,Y)$. With perfect correlation ($Y = f(X)$), we have $H(X|Y) = 0$--the correlated source needs zero rate.

**Derivation as perfect correlation.** In our model, derivation creates perfect correlation: if $L_d$ is derived from $L_s$, then $\text{value}(L_d) = f(\text{value}(L_s))$ deterministically. The "rate" of $L_d$ is effectively zero--it contributes no independent information. This is why derived locations do not contribute to DOF.

**Independence as zero correlation.** Independent locations have no correlation. Each can hold any value in $\mathcal{V}_F$. The total "rate" is DOF $\cdot H(F)$, but with DOF $> 1$, the locations can encode *different* values--incoherence.

### Side Information Bound

::: theorem
[]{#thm:side-info label="thm:side-info"} Given a state whose ambiguity class has size $k$, resolving to the correct value requires at least $\log_2 k$ bits of side information.
:::

::: proof
*Proof.* The ambiguity class presents $k$ internally supported alternatives. By Theorem [\[thm:oracle-arbitrary\]](#thm:oracle-arbitrary){reference-type="ref" reference="thm:oracle-arbitrary"}, no internal rule distinguishes them.

Let $S \in \{1, \ldots, k\}$ denote the index of the correct source. The decoder must determine $S$ to resolve correctly. Since $S$ is uniformly distributed over $k$ alternatives (by symmetry of the incoherent state): $$H(S) = \log_2 k$$

Any resolution procedure is a function $R: \text{State} \to \mathcal{V}_F$. Without side information $Y$: $$H(S | R(\text{State})) = H(S) = \log_2 k$$ because $R$ can be computed from the state, which contains no information about which source is correct.

With side information $Y$ that identifies the correct source: $$H(S | Y) = 0 \Rightarrow I(S; Y) = H(S) = \log_2 k$$

Therefore, side information must expose at least $\log_2 k$ bits' worth of distinguishable tags. ◻
:::

::: corollary
[]{#cor:dof1-zero-side label="cor:dof1-zero-side"} With DOF = 1, resolution requires 0 bits of side information.
:::

::: proof
*Proof.* With $k = 1$, there is one independent location. $H(S) = \log_2 1 = 0$. No uncertainty exists about the authoritative source. ◻
:::

::: corollary
[]{#cor:side-info-redundancy label="cor:side-info-redundancy"} The required side information equals $\log_2(1 + \rho)$ where $\rho$ is encoding redundancy: $$\text{Side information required} = \log_2(\text{DOF}) = \log_2(1 + \rho)$$
:::

**Connection to Slepian-Wolf.** In Slepian-Wolf coding, the decoder has side information $Y$ and decodes $X$ at rate $H(X|Y)$. Our setting inverts this: the decoder needs side information $S$ (source identity) to "decode" (resolve) which value is correct. The required side information is exactly the entropy of the source-selection variable.

**Connection to zero-error decoding.** In zero-error channel coding, the decoder must identify the transmitted message with certainty. Without sufficient side information (channel structure), this is impossible. Similarly, without $\log_2 k$ bits identifying the authoritative source, zero-error resolution is impossible.

::: example
[]{#ex:side-info-practice label="ex:side-info-practice"} Consider a configuration system with DOF = 3:

-   `config.yaml`: `threshold: 0.5`

-   `settings.json`: `"threshold": 0.7`

-   `params.toml`: `threshold = 0.6`

Resolution requires $\log_2 3 \approx 1.58$ bits of side information:

-   A priority ordering: "YAML $>$ JSON $>$ TOML" (encodes permutation $\to$ identifies source)

-   A timestamp comparison: "most recent wins" (encodes ordering $\to$ identifies source)

-   An explicit declaration: "params.toml is authoritative" (directly encodes source identity)

With DOF = 1, zero bits suffice--the single source is self-evidently authoritative.
:::

### Multi-Terminal Capacity Interpretation

The exact-consistency threshold (Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}) can be restated in multi-terminal language:

::: corollary
[]{#cor:multi-terminal label="cor:multi-terminal"} An encoding system achieves zero incoherence iff all terminals are perfectly correlated (every terminal's output is a deterministic function of one source terminal). Equivalently: the correlation structure must be a tree with one root.
:::

::: proof
*Proof.* Perfect correlation means DOF = 1 (only the root is independent). By Theorem [\[thm:capacity-achievability\]](#thm:capacity-achievability){reference-type="ref" reference="thm:capacity-achievability"}, this achieves zero incoherence. If any two terminals are independent (not perfectly correlated through the root), DOF $\geq 2$, and by Theorem [\[thm:capacity-converse\]](#thm:capacity-converse){reference-type="ref" reference="thm:capacity-converse"}, incoherence is reachable. ◻
:::

This connects to network information theory: in a multi-terminal network, achieving coherence requires complete dependence on a single source--no "multicast" of independent copies.

## Structure Theorems: The Derivation Lattice {#sec:derivation-structure}

The set of derivation relations on an encoding system has algebraic structure. We characterize this structure and its computational implications (UNQ1, UNQ1, UNQ1).

::: definition
[]{#def:derivation-relation label="def:derivation-relation"} A *derivation relation* $D \subseteq L \times L$ on locations $L$ is a directed relation where $(L_s, L_d) \in D$ means $L_d$ is derived from $L_s$. We require $D$ be acyclic (no location derives from itself through any chain).
:::

::: definition
[]{#def:dof-derivation label="def:dof-derivation"} Given derivation relation $D$, the degrees of freedom is: $$\text{DOF}(D) = |\{L : \nexists L'. (L', L) \in D\}|$$ The count of locations with no incoming derivation edges (source locations).
:::

::: theorem
[]{#thm:derivation-lattice label="thm:derivation-lattice"} The set of derivation relations on a fixed set of locations $L$, ordered by inclusion, forms a bounded lattice:

1.  **Bottom ($\bot$):** $D = \emptyset$ (no derivations, DOF = $|L|$)

2.  **Top ($\top$):** Maximal acyclic $D$ with DOF = 1 (all but one location derived)

3.  **Meet ($\land$):** $D_1 \land D_2 = D_1 \cap D_2$

4.  **Join ($\lor$):** $D_1 \lor D_2 =$ transitive closure of $D_1 \cup D_2$ (if acyclic)
:::

::: proof
*Proof.* **Bottom:** $\emptyset$ is trivially a derivation relation with all locations independent.

**Top:** For $n$ locations, a maximal acyclic relation has one source (root) and $n-1$ derived locations forming a tree or DAG. DOF = 1.

**Meet:** Intersection of acyclic relations is acyclic. The intersection preserves only derivations present in both.

**Join:** If $D_1 \cup D_2$ is acyclic, its transitive closure is the smallest relation containing both. If cyclic, join is undefined (partial lattice).

Bounded: $\emptyset \subseteq D \subseteq \top$ for all valid $D$. ◻
:::

::: theorem
[]{#thm:dof-antimonotone label="thm:dof-antimonotone"} DOF is anti-monotonic in the derivation lattice: $$D_1 \subseteq D_2 \Rightarrow \text{DOF}(D_1) \geq \text{DOF}(D_2)$$ More derivations imply fewer independent locations.
:::

::: proof
*Proof.* Adding a derivation edge $(L_s, L_d)$ to $D$ can only decrease DOF: if $L_d$ was previously a source (no incoming edges), it now has an incoming edge and is no longer a source. Sources can only decrease or stay constant as derivations are added. ◻
:::

::: corollary
[]{#cor:minimal-dof1 label="cor:minimal-dof1"} A derivation relation $D$ with DOF($D$) = 1 is *minimal* iff removing any edge increases DOF.
:::

**Computational implication:** Given an encoding system, there can be multiple DOF-1-achieving derivation structures. The minimal ones use the fewest derivation edges--the most economical way to achieve coherence.

**Representation model for complexity.** For the algorithmic results below, we assume the derivation relation $D$ is given explicitly as a DAG over the location set $L$. The input size is $|L| + |D|$, and all complexity bounds are measured in this explicit representation.

::: theorem
[]{#thm:dof-complexity label="thm:dof-complexity"} Given an encoding system with explicit derivation relation $D$:

1.  Computing DOF($D$) is $O(|L| + |D|)$ (linear in locations plus edges)

2.  Deciding if DOF($D$) = 1 is $O(|L| + |D|)$

3.  Finding a minimal DOF-1 extension of $D$ is $O(|L|^2)$ in the worst case
:::

::: proof
*Proof.* **(1) DOF computation:** Count locations with in-degree 0 in the DAG. Single pass over edges: $O(|D|)$ to compute in-degrees, $O(|L|)$ to count zeros.

**(2) DOF = 1 decision:** Compute DOF, compare to 1. Same complexity.

**(3) Minimal extension:** Must connect $k-1$ source locations to reduce DOF from $k$ to 1. Finding which connections preserve acyclicity requires reachability queries. Naive: $O(|L|^2)$. With better data structures (e.g., dynamic reachability): $O(|L| \cdot |D|)$ amortized. ◻
:::


# Derivation as the Capacity-Achieving Structure {#sec:ssot}

Having established the encoding model (Section [\[sec:epistemic\]](#sec:epistemic){reference-type="ref" reference="sec:epistemic"}), we now identify the structural mechanism that attains the exact-consistency regime: derivation induces perfect dependence, so derived locations add visibility without adding independent rate.

## Rate 1 as the Exact-Consistency Regime {#sec:ssot-def}

Rate $1$ is not merely a design preference. In the present model it is the exact-consistency threshold for facts encoded in systems with modification constraints (UNQ1, UNQ1, UNQ1).

::: definition
[]{#def:ssot label="def:ssot"} Encoding system $C$ achieves *optimal encoding rate* for fact $F$ iff: $$\text{DOF}(C, F) = 1$$ Equivalently: exactly one independent encoding location exists for $F$. All other encodings are derived.
:::

**Interpretation.** The language of "single authoritative source" is an application-level reading of a more basic IT statement: one independent source plus deterministic derivations is the unique zero-incoherence regime.

Equivalently, rate 1 means one independent encoding location and only deterministic views elsewhere.

::: corollary
[]{#thm:ssot-determinate label="thm:ssot-determinate"} If $\text{DOF}(C, F) = 1$, then for all reachable states of $C$, the value of $F$ is determinate: all encodings agree. *(This restates Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"} in terms of determinacy.)*
:::

As an application-level interpretation, this recovers Hunt & Thomas's "single, unambiguous, authoritative representation" [@hunt1999pragmatic].

Our contribution here is to show that the capacity-achieving structure is exactly the one in which all non-source locations are deterministic functions of a single source (UNQ1, UNQ1, UNQ1).

::: corollary
[]{#thm:ssot-optimal label="thm:ssot-optimal"} If $\text{DOF}(C, F) = 1$, then coherence restoration requires $O(1)$ updates. *(See Theorem [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"}.)*
:::

::: corollary
[]{#thm:ssot-unique label="thm:ssot-unique"} DOF = 1 is the unique rate guaranteeing coherence. *(See Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}.)*
:::

::: corollary
[]{#cor:no-redundancy label="cor:no-redundancy"} Multiple independent sources encoding the same fact permit incoherent states. DOF $> 1 \Rightarrow$ incoherence reachable.
:::

::: proof
*Proof.* Direct application of Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"}. With DOF $> 1$, independent locations can be modified separately, reaching states where they disagree. ◻
:::

See the formal Zero-Incoherence Capacity statement in Section [\[sec:capacity\]](#sec:capacity){reference-type="ref" reference="sec:capacity"} (Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}, UNQ1). The remainder of this section focuses on why derivation is the relevant dependence structure.

## Information-theoretic proof sketches {#sec:info-sketches}

We give concise proof sketches connecting the combinatorial DOF arguments to finite zero-error information-theoretic tools:

-   **Counting converse:** To show that limited side information cannot enable exact recovery of $F$, apply the finite counting converse (Theorem [\[thm:fano-converse\]](#thm:fano-converse){reference-type="ref" reference="thm:fano-converse"}, UNQ1). If $K$ ambiguous states must be distinguished using an $L$-bit side-information tag, exact recovery requires $K\le 2^L$, equivalently $L\ge \log_2 K$.

-   **Confusability graph:** Lemma [\[lem:confusability-clique\]](#lem:confusability-clique){reference-type="ref" reference="lem:confusability-clique"} converts combinatorial indistinguishability (cliques) into information lower bounds: in the finite zero-error model, a $k$-clique forces at least $k$ tag values (UNQ1, UNQ1); globally, the required tag alphabet is lower-bounded by both worst-case fiber size (UNQ1) and the observation-alphabet occupancy floor (UNQ1), equivalently $|\mathcal V|\le |\mathcal O|\cdot |\mathcal T|$ for any zero-error scheme (UNQ1). This gives a language-independent certificate that side information is insufficient in environments with limited introspection.

-   **DOF implication:** If side information cannot supply enough distinguishable tags for exact recovery, the system must retain multiple independent encodings (higher DOF) to achieve correctness under modifications. Higher DOF incurs $\Omega(n)$ manual edits (Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"}, UNQ1), completing the converse chain from information constraints to modification complexity.

## Rate-Complexity Tradeoff {#sec:ssot-vs-m}

The DOF metric creates a direct tradeoff between independent rate and manual synchronization cost.

**Question:** When fact $F$ changes, how many manual updates are required to restore coherence?

-   **DOF = 1:** $O(1)$ updates. The single source determines all derived locations automatically.

-   **DOF = $n > 1$:** $\Omega(n)$ updates. Each independent location must be synchronized manually.

This is a rate-complexity consequence of the exact-consistency threshold: higher independent rate incurs higher synchronization cost, while DOF = 1 minimizes that cost.

**Key insight:** Many locations can encode $F$ (high total encoding locations), but if DOF = 1, coherence restoration requires only 1 manual update. The derivation mechanism handles propagation automatically.

::: example
[]{#ex:ssot-large-m label="ex:ssot-large-m"} Consider an encoding system where a fact $F$ = "all processors must implement operation $P$" is encoded at 51 locations:

-   1 abstract specification location

-   50 concrete implementation locations

**Architecture A (DOF = 51):** All 51 locations are independent.

-   Modification complexity: Changing $F$ requires 51 manual updates

-   Coherence risk: After $k < 51$ updates, system is incoherent (partial updates)

-   Only after all 51 updates is coherence restored

**Architecture B (DOF = 1):** The abstract specification is the single source; implementations are derived.

-   Modification complexity: Changing $F$ requires 1 update (the specification)

-   Coherence guarantee: Derived locations update automatically via enforcement mechanism

-   The *specification* has a single authoritative source

**Realization:** Abstract base classes with enforcement (type checkers, runtime validation) achieve DOF = 1 for contract specifications. Changing the abstract method signature updates the contract; type checkers flag non-compliant implementations.

Note: Implementations are separate facts. DOF = 1 for the contract specification does not eliminate implementation updates--it ensures the specification itself is determinate.
:::

## Derivation: The Coherence Mechanism {#sec:derivation}

Derivation is the mechanism by which DOF is reduced without losing encodings. A derived location cannot diverge from its source, eliminating it as a source of incoherence.

::: definition
[]{#def:derivation label="def:derivation"} Location $L_{\text{derived}}$ is *derived from* $L_{\text{source}}$ for fact $F$ iff: $$\text{updated}(L_{\text{source}}) \rightarrow \text{automatically\_updated}(L_{\text{derived}})$$ No manual intervention is required. Coherence is maintained automatically.
:::

Derivation can occur at different times depending on the encoding system:

:::: center
::: tabularx
lY **Derivation Time** & **Examples Across Domains**\
Compile/Build time & C++ templates, Rust macros, database schema generation, infrastructure-as-code compilation\
Definition time & Python metaclasses, ORM model registration, dynamic schema creation\
Query/Access time & Database views, computed columns, lazy evaluation\
:::
::::

**Structural facts require definition-time derivation.** Structural facts (class existence, schema structure, service topology) are fixed when defined. Compile-time derivation that runs before the definition is fixed is too early (the declarative source is not yet fixed). Runtime is too late (structure already immutable). Definition-time is the unique opportunity for structural derivation---a consequence of timing trichotomy (UNQ1, UNQ1, UNQ1, UNQ1).

::: theorem
[]{#thm:derivation-excludes label="thm:derivation-excludes"} If $L_{\text{derived}}$ is derived from $L_{\text{source}}$, then $L_{\text{derived}}$ cannot diverge from $L_{\text{source}}$ and does not contribute to DOF.
:::

::: proof
*Proof.* By Definition [\[def:derivation\]](#def:derivation){reference-type="ref" reference="def:derivation"}, derived locations are automatically updated when the source changes. Let $L_d$ be derived from $L_s$. If $L_s$ encodes value $v$, then $L_d$ encodes $f(v)$ for some function $f$. When $L_s$ changes to $v'$, $L_d$ automatically changes to $f(v')$.

There is no reachable state where $L_s = v'$ and $L_d = f(v)$ with $v' \neq v$. Divergence is impossible. Therefore, $L_d$ does not contribute to DOF. ◻
:::

::: corollary
[]{#cor:metaprogramming label="cor:metaprogramming"} If all encodings of $F$ except one are derived from that one, then $\text{DOF}(C, F) = 1$ and coherence is guaranteed.
:::

::: proof
*Proof.* Let $L_s$ be the non-derived encoding. All other encodings $L_1, \ldots, L_k$ are derived from $L_s$. By Theorem [\[thm:derivation-excludes\]](#thm:derivation-excludes){reference-type="ref" reference="thm:derivation-excludes"}, none can diverge. Only $L_s$ is independent. Therefore, $\text{DOF}(C, F) = 1$, and by Theorem [\[thm:dof-one-coherence\]](#thm:dof-one-coherence){reference-type="ref" reference="thm:dof-one-coherence"}, coherence is guaranteed. ◻
:::

## Illustrative Realizations {#sec:ssot-patterns}

This subsection is illustrative only. It shows how the dependence structure appears in concrete systems, but the theorem itself is independent of these realizations.

**Software: Subclass Registration (Python)**

::: code
class Registry: \_registry = def \_\_init_subclass\_\_(cls, \*\*kwargs): Registry.\_registry\[cls.\_\_name\_\_\] = cls

class PNGHandler(Registry): \# Automatically registered pass
:::

**Encoding structure:**

-   Source: Class definition (declared once)

-   Derived: Registry dictionary entry (computed at definition time via `__init_subclass__`)

-   DOF = 1: Registry cannot diverge from class hierarchy

**Databases: Materialized Views**

::: code
CREATE TABLE users (id INT, name TEXT, created_at TIMESTAMP); CREATE MATERIALIZED VIEW user_count AS SELECT COUNT(\*) FROM users;
:::

**Encoding structure:**

-   Source: Base table `users`

-   Derived: Materialized view `user_count` (updated on refresh)

-   DOF = 1: View cannot diverge from base table (consistency guaranteed by DBMS)

**Configuration: Infrastructure as Code (Terraform)**

::: code
resource \"aws_instance\" \"app\" ami = \"ami-12345\" instance_type = \"t2.micro\"

output \"instance_ip\" value = aws_instance.app.public_ip
:::

**Encoding structure:**

-   Source: Resource declaration (authoritative configuration)

-   Derived: Output value (computed from resource state)

-   DOF = 1: Output cannot diverge from actual resource (computed at apply time)

**Common pattern:** In all cases, one location carries the independent value and the others are deterministic views computed at definition/build/query time. Manual synchronization disappears because the dependence structure, not human process, enforces consistency.


# Realizability Requirements for the Capacity-Achieving Regime {#sec:requirements}

This section identifies, at an abstract information-theoretic level, the two properties an encoding system must provide to realize the capacity-achieving regime. Concrete system-specific instantiations are treated as applications; here we isolate the abstract realizability conditions and their necessity/sufficiency proofs.

Informally, an encoding system provides a set of locations holding values and a space of allowed modifications. DOF = 1 is realizable when exactly one independent location exists (the source) and all other encodings are deterministic functions (derivations) of that source so divergence is impossible.

We show that two encoder properties are necessary and sufficient (UNQ1):

1.  **Causal update propagation:** updates to the source must automatically propagate to derived locations (eliminating transient incoherence windows);

2.  **Provenance observability:** the system must expose, to verification procedures, which locations are sources and which are derived (providing the side information necessary to verify DOF = 1).

The remainder of this section gives formal statements and proofs of necessity and sufficiency for these properties in the abstract model.

## Confusability and Side-Information {#sec:confusability}

To connect realizability to the information available at runtime, define the *confusability graph* for a fact $F$: vertices are distinct values of $F$, and an undirected edge joins two values $x,x'$ iff they are indistinguishable given the available side information (i.e., no observation of derived locations can reliably separate $x$ from $x'$).

::: lemma
[]{#lem:confusability-clique label="lem:confusability-clique"} If the confusability graph for $F$ contains a clique of size $k$, then any zero-error side-information scheme for distinguishing all $k$ values requires at least $k$ distinct tags, equivalently at least $\log_2 k$ bits of side information.
:::

::: proof
*Proof sketch.* Restrict $F$ to the $k$ values in the clique. In the finite zero-error setting, any zero-error tag assignment is a proper coloring of the confusability graph, so a $k$-clique forces at least $k$ distinct tag values (UNQ1, UNQ1). More generally, the Lean observer/tag layer now proves three stronger structural facts: exact recovery is equivalent to injectivity of the combined observation-plus-tag map (OBS1, OBS2); each observation fiber requires at most as many states as available tags (OBS3); and every clique therefore satisfies the direct alphabet bound $|\mathcal C|\le |\mathcal T|$ (OBS5). Consequently, the required tag alphabet is bounded below by the worst-case observation-fiber size, and globally every zero-error scheme must satisfy $|\mathcal V|\le |\mathcal O|\cdot |\mathcal T|$ (OBS4). Theorem [\[thm:fano-converse\]](#thm:fano-converse){reference-type="ref" reference="thm:fano-converse"} packages the same obstruction as a finite counting converse: if only $2^L$ tags are available, then no zero-error resolver can distinguish more than $2^L$ ambiguous states. ◻
:::

The confusability graph now has a fully mechanized finite zero-error interpretation: large cliques force large tag alphabets (OBS5), nontrivial cliques are impossible for observation-only architectures (OBS6), the worst-case fiber bound captures the same obstruction globally (OBS3), and a global counting converse gives $|\mathcal V|\le |\mathcal O|\cdot |\mathcal T|$ for any zero-error scheme (OBS4).

## The Structural Timing Constraint {#sec:timing}

For certain classes of facts--*structural facts*--there is a fundamental timing constraint that shapes realizability.

::: definition
[]{#def:structural-fact-req label="def:structural-fact-req"} A fact $F$ is *structural* if its encoding locations are fixed at the moment of definition. After definition, the structure cannot be retroactively modified--only new structures can be created.
:::

**Examples across domains:**

-   **Programming languages**: Class definitions, method signatures, inheritance relationships

-   **Databases**: Schema definitions, table structures, foreign key constraints

-   **Configuration systems**: Resource declarations, dependency specifications

-   **Version control**: Branch structures, commit ancestry

The key property: structural facts have a *definition moment* after which their encoding is immutable. This creates a timing constraint for derivation.

::: theorem
[]{#thm:timing-forces label="thm:timing-forces"} For structural facts, derivation must occur at or before the moment the structure is fixed.
:::

::: proof
*Proof.* Let $F$ be a structural fact. Let $t_{\text{fix}}$ be the moment $F$'s encoding is fixed. Any derivation $D$ that depends on $F$ must execute at some time $t_D$.

**Case 1**: $t_D < t_{\text{fix}}$. Derivation executes before $F$ is fixed. $D$ cannot derive from $F$ because $F$ does not yet exist.

**Case 2**: $t_D > t_{\text{fix}}$. Derivation executes after $F$ is fixed. $D$ can read $F$ but cannot modify structures derived from $F$--they are already fixed.

**Case 3**: $t_D = t_{\text{fix}}$. Derivation executes at the moment $F$ is fixed. $D$ can both read $F$ and create derived structures before they are fixed.

Therefore, structural derivation requires $t_D = t_{\text{fix}}$. ◻
:::

This timing constraint is the information-theoretic reason why derivation must be *causal*--triggered by the act of defining the source, not by later access (UNQ1, UNQ1).

## Requirement 1: Causal Update Propagation {#sec:causal-propagation}

::: definition
[]{#def:causal-propagation label="def:causal-propagation"} An encoding system has *causal update propagation* if changes to a source location automatically trigger updates to all derived locations, without requiring explicit synchronization commands.

Formally: let $L_s$ be a source location and $L_d$ a derived location. The system has causal propagation iff: $$\text{update}(L_s, v) \Rightarrow \text{automatically\_updated}(L_d, f(v))$$ where $f$ is the derivation function. No separate "propagate" or "sync" operation is required.
:::

**Information-theoretic interpretation:** Causal propagation is analogous to *channel coding with feedback*. In classical channel coding, the encoder sends a message and waits for acknowledgment. With feedback, the encoder can immediately react to channel state. Causal propagation provides "feedback" from the definition event to the derivation mechanism--the encoder (source) and decoder (derived locations) are coupled in real-time.

**Connection to multi-version coding:** Rashmi et al. [@rashmi2015multiversion] formalize consistent distributed storage where updates to a source must propagate to replicas while maintaining consistency. Their "multi-version code" requires that any $c$ servers can decode the latest common version--a consistency guarantee analogous to our coherence requirement. Causal propagation is the mechanism by which this consistency is maintained under updates.

**Why causal propagation is necessary:**

Without causal propagation, there exists a temporal window between source modification and derived location update. During this window, the system is incoherent--the source and derived locations encode different values.

::: theorem
[]{#thm:causal-necessary label="thm:causal-necessary"} Achieving DOF = 1 for structural facts requires causal update propagation.
:::

::: proof
*Proof.* By Theorem [\[thm:timing-forces\]](#thm:timing-forces){reference-type="ref" reference="thm:timing-forces"}, structural derivation must occur at definition time. Without causal propagation, derived locations are not updated when the source is defined. This means:

1.  The source exists with value $v$

2.  Derived locations have not been updated; they either do not exist yet or hold stale values

3.  The system is temporarily incoherent

For DOF = 1, incoherence must be *impossible*, not merely transient. Causal propagation eliminates the temporal window: derived locations are updated *as part of* the source definition, not after.

Contrapositive: If an encoding system lacks causal propagation, DOF = 1 for structural facts is unrealizable. ◻
:::

**Realizations across domains:**

::: center
  **Domain**            **Causal Propagation Mechanism**
  --------------------- -----------------------------------------------------------
  Python                `__init_subclass__`, metaclass `__new__`
  CLOS                  `:after` methods on class initialization
  Smalltalk             Class creation protocol, `subclass:` method
  Databases             Triggers on schema operations (PostgreSQL event triggers)
  Distributed systems   Consensus protocols (Paxos, Raft)
  Configuration         Terraform dependency graph, reactive bindings
:::

**Systems lacking causal propagation:**

-   **Java**: Annotations are metadata, not executable. No code runs at class definition.

-   **C++**: Templates expand at compile time but don't execute arbitrary user code.

-   **Go**: No hook mechanism. Interface satisfaction is implicit.

-   **Rust**: Proc macros run at compile time but generate static code, not runtime derivation.

## Requirement 2: Provenance Observability {#sec:provenance-observability}

::: definition
[]{#def:provenance-observability label="def:provenance-observability"} An encoding system has *provenance observability* if the system supports queries about derivation structure:

1.  What locations exist encoding a given fact?

2.  Which locations are sources vs. derived?

3.  What is the derivation relationship (which derived from which)?
:::

**Information-theoretic interpretation:** Provenance observability is the encoding-system analog of *side information at the decoder*. In Slepian-Wolf coding [@slepian1973noiseless], the decoder has access to correlated side information that enables decoding at rates below the source entropy. Provenance observability provides "side information" about the encoding structure itself--enabling verification that DOF = 1 holds.

Without provenance observability, the encoding system is a "black box"--you can read locations but cannot determine which are sources and which are derived. This makes DOF uncomputable from within the system.

::: theorem
[]{#thm:provenance-necessary label="thm:provenance-necessary"} Verifying that DOF = 1 holds requires provenance observability.
:::

::: proof
*Proof.* Verification of DOF = 1 requires confirming:

1.  All locations encoding fact $F$ are enumerable

2.  Exactly one location is independent (the source)

3.  All other locations are derived from that source

Step (1) requires querying what structures exist. Step (2) requires distinguishing sources from derived locations. Step (3) requires querying the derivation relationship.

Without provenance observability, none of these queries are answerable from within the system. DOF = 1 can hold but cannot be verified. Bugs in derivation logic go undetected until coherence violations manifest. ◻
:::

**Connection to coding theory:** In coding theory, a code's structure (generator matrix, parity-check matrix) must be known to the decoder. Provenance observability is analogous: the derivation structure must be queryable for verification.

**Realizations across domains:**

::: center
  **Domain**            **Provenance Observability Mechanism**
  --------------------- ---------------------------------------------------------
  Python                `__subclasses__()`, `__mro__`, `dir()`, `vars()`
  CLOS                  `class-direct-subclasses`, MOP introspection
  Smalltalk             `subclasses`, `allSubclasses`
  Databases             System catalogs (`pg_depend`), query plan introspection
  Distributed systems   Vector clocks, provenance tracking, `etcd` watch
  Configuration         Terraform `graph`, Kubernetes API server
:::

**Systems lacking provenance observability:**

-   **C++**: Cannot query "what types instantiated template `Foo<T>`?"

-   **Rust**: Proc macro expansion is opaque at runtime.

-   **TypeScript**: Types are erased. Runtime cannot query type relationships.

-   **Go**: No type registry. Cannot enumerate interface implementations.

## Independence of Requirements {#sec:independence}

The two requirements--causal propagation and provenance observability--are independent. Neither implies the other (UNQ1, UNQ1). This section is included because it explains when the abstract IT optimum can actually be instantiated; it is not needed to state the main threshold theorem itself.

::: theorem
[]{#thm:independence label="thm:independence"}

1.  An encoding system can have causal propagation without provenance observability

2.  An encoding system can have provenance observability without causal propagation
:::

::: proof
*Proof.* **(1) Causal without provenance:** Rust proc macros execute at compile time (causal propagation: definition triggers code generation). But the generated code is opaque at runtime--the program cannot query what was generated (no provenance observability).

**(2) Provenance without causal:** Java provides reflection (`Class.getMethods()`, `Class.getInterfaces()`)--provenance observability. But no code executes when a class is defined--no causal propagation. ◻
:::

This independence means both requirements must be satisfied for DOF = 1 realizability (UNQ1).

## The Realizability Theorem {#sec:realizability-theorem}

::: theorem
[]{#thm:ssot-iff label="thm:ssot-iff"} An encoding system $S$ can achieve verifiable DOF = 1 for structural facts if and only if:

1.  $S$ provides causal update propagation, AND

2.  $S$ provides provenance observability
:::

::: proof
*Proof.* $(\Rightarrow)$ **Necessity:** Suppose $S$ achieves verifiable DOF = 1 for structural facts.

-   By Theorem [\[thm:causal-necessary\]](#thm:causal-necessary){reference-type="ref" reference="thm:causal-necessary"}, $S$ must provide causal propagation

-   By Theorem [\[thm:provenance-necessary\]](#thm:provenance-necessary){reference-type="ref" reference="thm:provenance-necessary"}, $S$ must provide provenance observability

$(\Leftarrow)$ **Sufficiency:** Suppose $S$ provides both capabilities.

-   Causal propagation enables derivation at the right moment (when structure is fixed)

-   Provenance observability enables verification that all secondary encodings are derived

-   Therefore, DOF = 1 is achievable: create one source, derive all others causally, verify completeness via provenance queries

 ◻
:::

::: definition
[]{#def:dof-complete label="def:dof-complete"} An encoding system is *DOF-1-complete* if it satisfies both causal propagation and provenance observability. Otherwise it is *DOF-1-incomplete*.
:::

**Information-theoretic interpretation:** DOF-1-completeness is analogous to *channel capacity achievability*. A channel achieves capacity if there exist codes that approach the Shannon limit. An encoding system is DOF-1-complete if there exist derivation mechanisms that achieve the coherence-optimal rate (DOF = 1). The two requirements (causal propagation, provenance observability) are the "channel properties" that enable capacity achievement.

## Connection to Write-Once Memory Codes {#sec:wom-connection}

Our realizability requirements connect to *write-once memory (WOM) codes* [@rivest1982wom; @wolf1984wom], an established area of coding theory.

A WOM is a storage medium where bits can only transition in one direction (typically $0 \to 1$). Rivest and Shamir [@rivest1982wom] showed that WOMs can store more information than their apparent capacity by encoding multiple "writes" cleverly--the capacity for $t$ writes is $\log_2(t+1)$ bits per cell.

The connection to our framework:

-   **WOM constraint**: Bits can only increase (irreversible state change)

-   **Structural fact constraint**: Structure is fixed at definition (irreversible encoding)

-   **WOM coding**: Clever encoding enables multiple logical writes despite physical constraints

-   **DOF = 1 derivation**: Clever derivation enables multiple logical locations from one physical source

Both settings involve achieving optimal encoding under irreversibility constraints. WOM codes achieve capacity via coding schemes; DOF-1-complete systems achieve coherence via derivation mechanisms.

## The Logical Chain (Summary) {#sec:chain}

::: center
:::

**Mechanization status.** The core requirement chain is machine-checked in Lean 4; current build statistics are 12818 lines, 583 theorem/lemma statements, and 0 `sorry` placeholders.

## Concrete Impossibility Demonstration {#sec:impossibility}

We demonstrate exactly why DOF-1-incomplete systems cannot achieve DOF = 1 for structural facts.

**The structural fact:** "`PNGHandler` handles `.png` files."

This fact must be encoded in two places:

1.  The handler definition (where the handler is defined)

2.  The registry/dispatcher (where format$\to$handler mapping lives)

**Python (DOF-1-complete) achieves DOF = 1:**

::: code
class ImageHandler: \_registry =

def \_\_init_subclass\_\_(cls, format=None, \*\*kwargs): super().\_\_init_subclass\_\_(\*\*kwargs) if format: ImageHandler.\_registry\[format\] = cls \# DERIVED (causal)

class PNGHandler(ImageHandler, format=\"png\"): \# SOURCE def load(self, path): \...
:::

**Causal propagation:** When `class PNGHandler` executes, `__init_subclass__` fires immediately, adding the registry entry. No temporal gap.

**Provenance observability:** `ImageHandler.__subclasses__()` returns all handlers. The derivation structure is queryable.

**DOF = 1**: The `format="png"` in the class definition is the single source. The registry entry is derived causally. Adding a new handler requires changing exactly one location.

**Java (DOF-1-incomplete) cannot achieve DOF = 1:**

::: code
// File 1: PNGHandler.java \@Handler(format = \"png\") // Metadata, not executable public class PNGHandler implements ImageHandler \...

// File 2: HandlerRegistry.java (SEPARATE SOURCE) public class HandlerRegistry static register(\"png\", PNGHandler.class); // Manual
:::

**No causal propagation:** The `@Handler` annotation is data, not code. Nothing executes when the class is defined.

**Provenance partially present:** Java has reflection, but cannot enumerate "all classes with `@Handler`" without classpath scanning.

**DOF = 2**: The annotation and the registry are independent encodings. Either can be modified without the other. Incoherence is reachable.

::: theorem
[]{#thm:generated-second label="thm:generated-second"} A generated source file constitutes an independent encoding, not a derivation. Code generation does not achieve DOF = 1.
:::

::: proof
*Proof.* Let $E_1$ be the annotation on `PNGHandler.java`. Let $E_2$ be the generated `HandlerRegistry.java`.

Test: If $E_2$ is deleted or modified, does system behavior change? **Yes**--the handler is not registered.

Test: Can $E_2$ diverge from $E_1$? **Yes**--$E_2$ is a separate file that can be edited, fail to generate, or be stale.

Therefore, $E_1$ and $E_2$ are independent encodings. The fact that $E_2$ was *generated from* $E_1$ does not make it derived in the DOF sense, because:

1.  $E_2$ exists as a separate artifact that can diverge

2.  The generation process is external to the runtime and can be bypassed

3.  There is no causal coupling--modification of $E_1$ does not automatically update $E_2$

Contrast with Python: the registry entry exists only in memory, created causally by the class statement. There is no second file. DOF = 1. ◻
:::

## Summary: The Information-Theoretic Requirements {#sec:req-summary}

:::: center
::: tabularx
lYY **Requirement** & **IT Interpretation** & **Why Necessary**\
Causal propagation & Channel with feedback; encoder-decoder coupling & Eliminates temporal incoherence window\
Provenance observability & Side information at decoder; codebook visibility & Enables DOF verification\
:::
::::

Both requirements are necessary. Neither is sufficient alone. Together they enable DOF-1-complete encoding systems that achieve the coherence-optimal rate.


# Application: Programming-Language Instantiation {#sec:evaluation}

We instantiate Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"} in the domain of programming languages. This section is intentionally application-level: the abstract IT results are complete without it, and the goal here is only to show how the realizability theorem specializes once a language's definition-time hooks and introspection capabilities are fixed.

::: corollary
[]{#cor:lang-realizability label="cor:lang-realizability"} A programming language can realize DOF = 1 for structural facts iff it provides both (i) definition-time hooks and (ii) introspectable derivations. This is the direct instantiation of Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}.
:::

**Instantiation map.** In the abstract model, an independent encoding is a location that can diverge under edits. In programming languages, structural facts are encoded at definition sites; *definition-time hooks* implement derivation (automatic propagation), and *introspection* implements provenance observability. Thus DEF corresponds to causal propagation and INTRO corresponds to queryable derivations; DOF = 1 is achievable exactly when both are present.

We instantiate this corollary over a representative language class (Definition [\[def:mainstream\]](#def:mainstream){reference-type="ref" reference="def:mainstream"}).

::: definition
[]{#def:mainstream label="def:mainstream"} A language is *mainstream* iff it appears in the top 20 of at least two of the following indices consistently over 5+ years:

1.  TIOBE Index [@tiobe2024] (monthly language popularity)

2.  Stack Overflow Developer Survey (annual)

3.  GitHub Octoverse (annual repository statistics)

4.  RedMonk Programming Language Rankings (quarterly)
:::

## Evaluation Criteria {#sec:criteria}

The abstract realizability conditions (causal update propagation and provenance observability) map directly to concrete language capabilities (definition-time hooks and runtime introspection). We summarize this mapping briefly and defer the full language-by-language evaluation, extended code examples, and detailed rationale to Supplement A.

## Summary Classification {#sec:classification-summary}

Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"} partitions languages into two classes:

:::: center
::: tabularx
@\>p0.18YY@ **Language** & **Def-time hooks** & **Introspection**\
\
Python & UNQ1 & UNQ1\
CLOS & `:after` methods & MOP queries\
Smalltalk & class creation protocol & `subclasses`\
\
Java & -- & reflection\
C++ & -- & --\
Rust & proc macros (compile-time) & --\
Go & -- & --\
:::
::::

**Interpretation.** DOF-1-complete languages can realize the abstract capacity-achieving structure for structural facts using language-native mechanisms. DOF-1-incomplete languages require external tooling (code generation, IDE refactoring) which operates outside language semantics and can be bypassed (cf. Theorem [\[thm:independence\]](#thm:independence){reference-type="ref" reference="thm:independence"} on why external tools do not establish derivation).

Viewed after formalization, the two requirements may appear straightforward. In this mainstream set, only Python satisfies both; Java has introspection without definition-time hooks, Rust has compile-time hooks without runtime introspection, and C++ and Go have neither.

Supplement A contains the complete evaluation with justifications, worked code examples demonstrating each mechanism, and discussion of edge cases.


# Rate-Complexity Bounds {#sec:bounds}

This section translates the exact-consistency threshold into an operational consequence: independent rate governs manual synchronization cost. The key point is not merely that rate $1$ is coherent, but that moving above that threshold creates a provable complexity gap that grows with system size (UNQ1).

## Cost Model {#sec:cost-model}

::: definition
[]{#def:cost-model label="def:cost-model"} Let $\delta_F$ be a modification to fact $F$ in encoding system $C$. The *effective modification complexity* $M_{\text{effective}}(C, \delta_F)$ is the number of syntactically distinct edit operations that must be performed manually. Formally: $$M_{\text{effective}}(C, \delta_F) = |\{L \in \text{Locations}(C) : \text{requires\_manual\_edit}(L, \delta_F)\}|$$ where $\text{requires\_manual\_edit}(L, \delta_F)$ holds iff location $L$ must be updated manually (not by automatic derivation) to maintain coherence after $\delta_F$.
:::

**Unit of cost:** One edit = one syntactic modification to one location. We count locations, not keystrokes or characters. This abstracts over edit complexity to focus on the scaling behavior.

**What we measure:** Manual edits only. Derived locations that update automatically have zero cost. This isolates the operational consequence of independent information: if a location carries its own freely editable value, it contributes to synchronization burden.

**Asymptotic parameter:** We measure scaling in the number of encoding locations for fact $F$. Let $n = |\{L \in C : \text{encodes}(L, F)\}|$ and $k = \text{DOF}(C, F)$. Bounds of $O(1)$ and $\Omega(n)$ are in this parameter; in particular, the lower bound uses $n = k$ independent locations.

## Upper Bound: DOF = 1 Achieves O(1) {#sec:upper-bound}

::: theorem
[]{#thm:upper-bound label="thm:upper-bound"} For an encoding system with DOF = 1 for fact $F$: $$M_{\text{effective}}(C, \delta_F) = O(1)$$ Effective modification complexity is constant regardless of system size.
:::

::: proof
*Proof.* Let $\text{DOF}(C, F) = 1$. By Definition [\[def:ssot\]](#def:ssot){reference-type="ref" reference="def:ssot"}, $C$ has exactly one independent encoding location. Let $L_s$ be this single independent location.

When $F$ changes:

1.  Update $L_s$ (1 manual edit)

2.  All derived locations $L_1, \ldots, L_k$ are automatically updated by the derivation mechanism

3.  Total manual edits: 1

The number of derived locations $k$ can grow with system size, but the number of *manual* edits remains 1. Therefore, $M_{\text{effective}}(C, \delta_F) = O(1)$. ◻
:::

**Note on "effective" vs. "total" complexity:** Total modification complexity $M(C, \delta_F)$ counts all locations that change. Effective modification complexity counts only manual edits. With DOF = 1, total complexity can be $O(n)$ (many derived locations change), but effective complexity is $O(1)$ (one manual edit).

## Lower Bound: DOF $>$ 1 Requires $\Omega(n)$ {#sec:lower-bound}

::: theorem
[]{#thm:lower-bound label="thm:lower-bound"} For an encoding system with DOF $>$ 1 for fact $F$, if $F$ is encoded at $n$ independent locations: $$M_{\text{effective}}(C, \delta_F) = \Omega(n)$$
:::

::: proof
*Proof.* Let $\text{DOF}(C, F) = n$ where $n > 1$.

By Definition [\[def:independent\]](#def:independent){reference-type="ref" reference="def:independent"}, the $n$ encoding locations are independent--updating one does not automatically update the others. When $F$ changes:

1.  Each of the $n$ independent locations must be updated manually

2.  No automatic propagation exists between independent locations

3.  Total manual edits: $n$

Therefore, $M_{\text{effective}}(C, \delta_F) = \Omega(n)$. ◻
:::

## Information-theoretic converse (finite counting) {#sec:info-converse}

To make the converse direction genuinely information-theoretic, we give a finite zero-error counting converse showing that insufficient side-information alphabet size makes exact recovery impossible (UNQ1, UNQ1). This is the bridge from ambiguity to complexity: if side information is insufficient, exact resolution fails, and systems that still demand correctness must pay through additional independent encodings and manual synchronization.

::: remark
The results in this subsection are formalized in the source Lean tree as finite zero-error counting theorems rather than probabilistic Fano inequalities. The core capacity, side-information, realizability, and complexity chains are machine-checked in that exact form.
:::

::: theorem
[]{#thm:fano-converse label="thm:fano-converse"} Let $F$ range over $K$ possible values. Suppose exact resolution is attempted using an $L$-bit side-information tag and a decoder that must recover the correct value with zero error from that tag and a fixed observation transcript. Then $$K \le 2^L.$$ Equivalently, exact recovery of $K$ ambiguous states requires at least $\log_2 K$ bits of side information.
:::

::: proof
*Proof sketch.* There are only $2^L$ possible tags. In the strengthened Lean observer/tag model, exact recovery is equivalent to injectivity of the combined observation-plus-tag map (OBS1, OBS2). If the observation transcript is fixed, this reduces to injectivity of the tag map on the ambiguous states themselves. Hence two distinct values cannot share one tag under zero-error decoding, and injectivity is possible only when $K\le 2^L$. ◻
:::

This converse formalizes the intuition used in the main text: unless the side-information channel has enough distinct tags to separate all ambiguous states, exact recovery is impossible. The modification-complexity consequence comes from the architectural fallback: when exact recovery cannot be certified from side information, systems that still require correctness must maintain or consult additional independent sources, which raises DOF and therefore update cost.

## Information-constrained DOF lower bound {#sec:info-dof}

The following lemma makes that link explicit.

::: lemma
[]{#lem:info-dof label="lem:info-dof"} Let $F$ range over $K$ possible values. If the available side-information scheme exposes at most $2^L$ distinguishable tags with $K>2^L$, then no zero-error resolver can recover $F$ from those tags alone. Any architecture that nevertheless guarantees correctness must therefore retain additional independent encodings for some subset of values, hence DOF $>1$ on that subset. Consequently, for facts encoded at $n$ independent locations the effective modification complexity satisfies $M_{\text{effective}}=\Omega(n)$.
:::

::: proof
*Proof sketch.* By Theorem [\[thm:fano-converse\]](#thm:fano-converse){reference-type="ref" reference="thm:fano-converse"}, if $K>2^L$ then the side-information tags are too small to support exact recovery of all $K$ possibilities. The strengthened Lean architecture layer makes this explicit: every exact-recovery architecture carries a formal support count, and that support count is lower-bounded both globally by the observation/support product bound (OBS7) and locally by any confusability clique (OBS8, OBS9). In particular, observation-only architectures (support count $=1$) are impossible on nontrivial cliques (OBS10). The new bridge theorem then identifies this support count with a concrete instance of the paper's 'Dof.dof' semantics under a derivation-free support architecture (OBS11); hence nontrivial cliques force a formal DOF strictly above one (OBS12). Therefore, if correctness is still required under updates, the architecture must expose additional independently accessible discriminating support; in the paper's DOF reading, this means moving above the single-source regime. Once DOF$>1$ over a set of $n$ independent locations, Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"} implies $M_{\text{effective}}=\Omega(n)$. ◻
:::

## Worked example: finite tag budget {#sec:worked-mi}

Consider a fact $F$ with $K=4$ possible values. Suppose the available side-information mechanism supplies only a 1-bit tag, so at most $2^1=2$ distinct tags are available.

Apply Theorem [\[thm:fano-converse\]](#thm:fano-converse){reference-type="ref" reference="thm:fano-converse"}. Exact recovery would require $$4 \le 2^1,$$ which is false. So 1 bit of side information cannot resolve the 4-way ambiguity exactly.

Interpretation: with only 2 available tags for 4 possible values, some pair of values must collide. Therefore, to guarantee exact recovery one must either supply more side information (increase $L$ until $2^L\ge 4$) or enrich the architecture with a nontrivial auxiliary channel; in the paper's systems reading, that means additional independently accessible discriminating information, which in turn raises manual modification costs per Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"}.

By contrast, a 2-bit tag budget gives $2^2=4$ tags, which is just enough to distinguish all four values in principle.

The same reasoning extends to a finite relaxed-error setting where exact recovery is only required on a designated subset of states: any confusability clique that must still be recovered exactly obeys the same tag-alphabet lower bound (OBS13).

More generally, the source proof tree now contains an explicit finite distribution/error layer. For a finite source distribution with point-mass ceiling $m$, the total probability of exactly recovered states is bounded by $(|\mathcal O|\cdot |\mathcal T|)m$ (PRB2), so the error probability is bounded below by $1-(|\mathcal O|\cdot |\mathcal T|)m$ (PRB3). For families of instances with a uniform budget-mass gap, this yields a fully mechanized non-vanishing-error theorem (PRB6).

For the uniform finite source, these bounds sharpen into a direct weak-Fano-style converse: success probability is at most the observation/tag budget fraction (PRB8), hence any decoder with error at most $\varepsilon$ must satisfy $$1-\varepsilon \le \frac{|\mathcal O|\,|\mathcal T|}{K},$$ formalized in Lean as PRB9. The strengthened source proofs also identify the exact success probability under the uniform source with the fraction of states decoded exactly (PRB11, PRB12), yielding a cardinality form of the same converse: low error forces a large exactly recovered subset (PRB13), which is then bounded by the observation/tag budget to recover the weak-Fano inequality (PRB14). Families with a uniform gap below this threshold cannot have vanishing error (PRB10).

The entropy layer now goes one step further: a fully mechanized partition identity shows that for the uniform source, the success/failure split satisfies $$\log K = h(P_e) + (1-P_e)\log |S| + P_e\log |F|,$$ where $S$ is the exactly recovered subset and $F$ its complement (PRB15). Combining this identity with the exact success-set budget bound yields an explicit finite Fano-style inequality in the source proof tree: $$\log K \le h(P_e) + (1-P_e)\log(|\mathcal O||\mathcal T|) + P_e\log(K-1)$$ for the uniform finite source with nontrivial success/failure partition (PRB16). In the observation-only specialization this reduces to a $q$-ary entropy bound (PRB17).

The source proofs then sharpen the observation-only case further: for a uniform $K$-state source, observation-only recovery succeeds with probability at most $1/K$ (PRB18) and therefore has error probability at least $1-1/K$ (PRB19).

**Tightness (Achievability + Converse).** Theorems [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"} and [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"} together show that the operational cost transition at rate $1$ is sharp: rate $1$ achieves constant manual cost, while any architecture with more than one independent location incurs linear cost in the number of independent encodings (UNQ1, UNQ1).

## The Unbounded Gap {#sec:gap}

::: theorem
[]{#thm:unbounded-gap label="thm:unbounded-gap"} The ratio of modification complexity between DOF-1-incomplete and DOF-1-complete architectures grows without bound: $$\lim_{n \to \infty} \frac{M_{\text{DOF}>1}(n)}{M_{\text{DOF}=1}} = \lim_{n \to \infty} \frac{n}{1} = \infty$$
:::

::: proof
*Proof.* By Theorem [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"}, $M_{\text{DOF}=1} = O(1)$. Specifically, $M_{\text{DOF}=1} = 1$ for any system size.

By Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"}, $M_{\text{DOF}>1}(n) = \Omega(n)$ where $n$ is the number of independent encoding locations.

The ratio is: $$\frac{M_{\text{DOF}>1}(n)}{M_{\text{DOF}=1}} = \frac{n}{1} = n$$

As $n \to \infty$, the ratio $\to \infty$. The gap is unbounded. ◻
:::

::: corollary
[]{#cor:arbitrary-reduction label="cor:arbitrary-reduction"} For any constant $k$, there exists a system size $n$ such that DOF = 1 provides at least $k\times$ reduction in modification complexity.
:::

::: proof
*Proof.* Choose $n = k$. Then $M_{\text{DOF}>1}(n) = n = k$ and $M_{\text{DOF}=1} = 1$. The reduction factor is $k/1 = k$. ◻
:::

## The (R, C, P) Tradeoff Space {#sec:rcp-tradeoff}

We now summarize the tradeoff space induced by the model.

::: definition
[]{#def:rcp-tradeoff label="def:rcp-tradeoff"} For an encoding system, define:

-   $R$ = *Rate* (DOF): Number of independent encoding locations

-   $C$ = *Complexity*: Manual modification cost per change

-   $P$ = *Coherence indicator*: $P = 1$ iff no incoherent state is reachable; otherwise $P = 0$

The *(R, C, P) tradeoff space* is the set of achievable $(R, C, P)$ tuples.
:::

::::: theorem
[]{#thm:operating-regimes label="thm:operating-regimes"} The (R, C, P) space has three distinct operating regimes:

:::: center
::: tabularx
cccY **Rate** & **Complexity** & **Coherence** & **Interpretation**\
$R = 0$ & $C = 0$ & $P =$ undefined & Fact not encoded\
$R = 1$ & $C = O(1)$ & $P = 1$ & **Optimal (capacity-achieving)**\
$R > 1$ & $C = \Omega(R)$ & $P = 0$ & Above capacity\
:::
::::
:::::

::: proof
*Proof.* **$R = 0$:** No encoding exists. Complexity is zero (nothing to modify), but coherence is undefined (nothing to be coherent about).

**$R = 1$:** By Theorem [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"}, $C = O(1)$. By Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}, $P = 1$ (coherence guaranteed). This is the capacity-achieving regime.

**$R > 1$:** By Theorem [\[thm:lower-bound\]](#thm:lower-bound){reference-type="ref" reference="thm:lower-bound"}, $C = \Omega(R)$. By Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"}, incoherent states are reachable, so $P = 0$. ◻
:::

::: definition
[]{#def:pareto-frontier label="def:pareto-frontier"} A point $(R, C, P)$ is *Pareto optimal* if no other achievable point dominates it (lower $R$, lower $C$, or higher $P$ without worsening another dimension).

The *Pareto frontier* is the set of all Pareto optimal points.
:::

::: theorem
[]{#thm:pareto-optimal label="thm:pareto-optimal"} $(R=1, C=1, P=1)$ is the unique Pareto optimal point for encoding systems requiring coherence ($P = 1$).
:::

::: proof
*Proof.* We show $(1, 1, 1)$ is Pareto optimal and unique:

**Existence:** By Theorems [\[thm:upper-bound\]](#thm:upper-bound){reference-type="ref" reference="thm:upper-bound"} and [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}, the point $(1, 1, 1)$ is achievable.

**Optimality:** Consider any other achievable point $(R', C', P')$ with $P' = 1$:

-   If $R' = 0$: Fact is not encoded (excluded by requirement)

-   If $R' = 1$: Same as $(1, 1, 1)$ (by uniqueness of $C$ at $R=1$)

-   If $R' > 1$: By Theorem [\[thm:dof-gt-one-incoherence\]](#thm:dof-gt-one-incoherence){reference-type="ref" reference="thm:dof-gt-one-incoherence"}, $P' < 1$, contradicting $P' = 1$

**Uniqueness:** No other point achieves $P = 1$ except $R = 1$. ◻
:::

**Information-theoretic interpretation.** If one uses $1-P$ as a coarse distortion surrogate, then the zero-distortion boundary collapses to a single point: $R=1$ is the only rate achieving perfect coherence.

::: corollary
[]{#cor:no-tradeoff label="cor:no-tradeoff"} Unlike rate-distortion where you can trade rate for distortion, there is no tradeoff at $P = 1$ (perfect coherence). The only option is $R = 1$.
:::

::: proof
*Proof.* Direct consequence of Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}. ◻
:::

**Comparison to rate-distortion.** In rate-distortion theory:

-   You can achieve lower distortion with higher rate (more bits)

-   The rate-distortion function $R(D)$ is monotonically decreasing

-   $D = 0$ (lossless) requires $R = H(X)$ (source entropy)

In our framework:

-   You *cannot* achieve higher coherence ($P$) with more independent locations

-   Higher rate ($R > 1$) *eliminates* coherence guarantees ($P = 0$)

-   $P = 1$ (perfect coherence) requires $R = 1$ exactly

The key difference is that extra independent representations increase ambiguity unless they are coordinated by derivation. In this setting, uncontrolled redundancy hurts exact consistency.

## Practical Implications {#sec:practical-implications}

The unbounded gap has practical implications, but these should be read as consequences of the abstract rate/computation result rather than as the main theorem of the paper:

**1. DOF = 1 matters more at scale.** For small systems ($n = 3$), the difference between 3 edits and 1 edit is minor. For large systems ($n = 50$), the difference between 50 edits and 1 edit is significant.

**2. The gap compounds over time.** Each modification to fact $F$ incurs the complexity cost. If $F$ changes $m$ times over the system lifetime, total cost is $O(mn)$ with DOF $>$ 1 vs. $O(m)$ with DOF = 1.

**3. The gap affects error rates.** Each manual edit is an opportunity for error. With $n$ edits, the probability of at least one error is $1 - (1-p)^n$ where $p$ is the per-edit error probability. As $n$ grows, this approaches 1.

:::: example
[]{#ex:error-rate label="ex:error-rate"} Assume a 1% error rate per edit ($p = 0.01$).

::: center
   **Edits ($n$)**   **P(at least one error)**   **Architecture**
  ----------------- --------------------------- ------------------
          1                    1.0%                  DOF = 1
         10                    9.6%                  DOF = 10
         50                    39.5%                 DOF = 50
         100                   63.4%                DOF = 100
:::

With 50 independent encoding locations (DOF = 50), there is a 39.5% chance of introducing an error when modifying fact $F$. With DOF = 1, the chance is 1%.
::::

## Amortized Analysis {#sec:amortized}

The complexity bounds assume a single modification. Over the lifetime of an encoding system, facts are modified many times (UNQ1).

::: theorem
[]{#thm:amortized label="thm:amortized"} Let fact $F$ be modified $m$ times over the system lifetime. Let $n$ be the number of independent encoding locations. Total modification cost is:

-   DOF = 1: $O(m)$

-   DOF = $n > 1$: $O(mn)$
:::

::: proof
*Proof.* Each modification costs $O(1)$ with DOF = 1 and $O(n)$ with DOF = $n$. Over $m$ modifications, total cost is $m \cdot O(1) = O(m)$ with DOF = 1 and $m \cdot O(n) = O(mn)$ with DOF = $n$. ◻
:::

For a fact modified 100 times with 50 independent encoding locations:

-   DOF = 1: 100 edits total

-   DOF = 50: 5,000 edits total

The 50$\times$ reduction factor applies to every modification, compounding over the system lifetime.


# Application: Realizability Patterns (Worked Example) {#sec:empirical}

This section contained an extended worked example and multiple detailed code snippets illustrating realizability patterns from the OpenHCS case study. For the revised IT-first manuscript we move the full worked example, all code excerpts, and the detailed DOF measurements to Supplement A ("Practical Patterns and Case Study").

Below we give only a short summary and pointer to the supplement; the complete instantiation, PR traces, and verifiable diffs are available in Supplement A.

**Summary (short):**

-   Four recurring patterns realize DOF = 1: contract enforcement, automatic registration, automatic discovery, and introspection-driven code generation.

-   A publicly verifiable OpenHCS pull request (PR 44) demonstrates a 47$\to$`<!-- -->`{=html}1 DOF reduction; full diffs and measurements are in Supplement A.

-   The worked examples illustrate why both definition-time hooks and runtime introspection are necessary for DOF = 1; language-by-language impossibility notes are in Supplement A.

For the interested reader, Supplement A contains the complete before/after code, the methodology, measurement tables, and links to the public PR and repository snapshots.


# Related Work {#sec:related}

This section surveys related work across zero-error and multi-terminal source coding, interactive information theory, distributed systems, realizability mechanisms, and formal methods. The emphasis is on the IT lineage; application-side references are included only where they clarify realizability.

## Zero-Error and Multi-Terminal Source Coding {#sec:related-source-coding}

Our exact-consistency threshold is intended as an extension of classical source-coding ideas to interactive multi-terminal systems.

**Zero-Error Capacity.** Shannon [@shannon1956zero] introduced zero-error capacity: the maximum rate achieving exactly zero error probability. Körner [@korner1973graphs] connected this to graph entropy, and Lovász [@lovasz1979shannon] characterized the Shannon capacity of the pentagon graph. Our zero-incoherence capacity is the storage analog: the maximum encoding rate achieving exactly zero incoherence probability. The achievability/converse structure (Theorems [\[thm:capacity-achievability\]](#thm:capacity-achievability){reference-type="ref" reference="thm:capacity-achievability"}, [\[thm:capacity-converse\]](#thm:capacity-converse){reference-type="ref" reference="thm:capacity-converse"}) parallels zero-error proofs. The key parallel: zero-error capacity requires distinguishability between codewords; zero-incoherence capacity requires indistinguishability (all locations must agree).

**Multi-Terminal Source Coding.** Slepian and Wolf [@slepian1973noiseless] characterized distributed encoding of correlated sources: sources $(X, Y)$ can be encoded at rates satisfying $R_X \geq H(X|Y)$ when $Y$ is decoder side information. We model encoding locations as terminals (Section [\[sec:side-information\]](#sec:side-information){reference-type="ref" reference="sec:side-information"}). Derivation introduces *perfect correlation*: a derived terminal's output is a deterministic function of its source, so $H(L_d | L_s) = 0$. The capacity result shows that only complete correlation (all terminals derived from one source) achieves zero incoherence.

**Multi-Version Coding.** Rashmi et al. [@rashmi2015multiversion] formalize consistent distributed storage where multiple versions must be accessible while maintaining consistency. Their setting quantifies a storage cost for consistency; ours quantifies an independent-rate and side-information cost for exact consistency under modification.

**Classical Source Coding.** Shannon [@shannon1948mathematical] established source coding theory for static data. Slepian and Wolf [@slepian1973noiseless] extended to distributed sources with correlated side information, proving that joint encoding of $(X, Y)$ can achieve rate $H(X|Y)$ for $X$ when $Y$ is available at the decoder.

Our provenance observability requirement (Section [\[sec:provenance-observability\]](#sec:provenance-observability){reference-type="ref" reference="sec:provenance-observability"}) is the encoding-system analog: the decoder (verification procedure) has "side information" about the derivation structure, enabling verification of DOF = 1 without examining all locations independently.

**Rate-Distortion Theory.** Cover and Thomas [@cover2006elements] formalize the rate-distortion function $R(D)$. Our rate-complexity tradeoff is not a full distortion theory, but it plays a similar organizational role: independent rate governs the operational cost of maintaining exact consistency.

**Interactive Information Theory.** The BIRS workshop [@birs2012interactive] identified interactive information theory as an emerging area combining source coding, channel coding, and directed information. Ma and Ishwar [@ma2011distributed] showed that interaction can reduce rate for function computation. Xiang [@xiang2013interactive] studied interactive schemes including feedback channels.

Our framework extends this to *storage* rather than communication: encoding systems where the encoding itself is modified over time, requiring coherence maintenance.

#### Closest prior work and novelty.

The closest IT lineage is multi-version coding and zero-error/interactive source coding. These settings address consistency or decoding with side information, but they do not model *modifiable* encodings with a coherence constraint over time. Our contribution is a formal encoding model with explicit modification operations, an exact-consistency characterization with achievability/converse structure, a side-information lower bound, an iff realizability characterization, and rate--complexity consequences.

## Distributed Systems Consistency {#sec:related-distributed}

Distributed-systems impossibility results provide useful structural analogies. In particular, our CAP/FLP-style statements isolate how independent updates create ambiguity and how ambiguity blocks internally justified resolution without side information.

## Computational Reflection and Metaprogramming {#sec:related-meta}

**Metaobject protocols and reflection.** Kiczales et al. [@kiczales1991art] and Smith [@smith1984reflection] provide the classical foundations for systems that can execute code at definition time and introspect their own structure. These mechanisms correspond directly to causal propagation and provenance observability in our realizability theorem, explaining why MOP-equipped languages admit DOF = 1 for structural facts.

## Application-Level Design Principles {#sec:related-software}

Application-level design principles such as DRY [@hunt1999pragmatic], information hiding [@parnas1972criteria], and duplication analyses [@fowler1999refactoring; @roy2007survey] motivate coherence and single-source design. These links are interpretive only; the proofs do not rely on them.

## Formal Methods {#sec:related-formal}

Our Lean 4 [@demoura2021lean4] formalization follows the tradition of mechanized theory (e.g., Pierce [@pierce2002types], Winskel [@winskel1993semantics], CompCert [@leroy2009compcert]), but applies it to an information-theoretic encoding model.

## Novelty and IT Contribution {#sec:novelty}

To our knowledge, this is the first work to:

1.  **Characterize the exact-consistency threshold**--$C_0 = 1$ exactly, with explicit achievability and converse.

2.  **Quantify side information for resolution**--$\geq \log_2 k$ bits for a $k$-way ambiguity class (Theorem [\[thm:side-info\]](#thm:side-info){reference-type="ref" reference="thm:side-info"}).

3.  **Characterize realizability**--causal propagation and provenance observability are necessary and sufficient to realize the threshold in concrete systems (Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}).

4.  **Establish rate-complexity consequences**--$O(1)$ at rate $1$ versus $\Omega(n)$ above it, with unbounded gap (Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"}).

**What is new:** The setting (interactive multi-location encoding with modifications), the exact-consistency characterization for this setting, the side-information bound, the encoder realizability iff, and the machine-checked proofs. The application instantiations are corollaries illustrating the abstract theory.


# Conclusion {#sec:conclusion}

We have studied exact consistency in interactive multi-location encoding systems through an information-theoretic lens. The key takeaway is that ambiguity, not duplication alone, is the central IT object: once multiple internally supported values exist, exact resolution requires quantifiable side information.

The main contributions are:

**1. Side Information Bound:** We prove that resolution of a $k$-way ambiguity class requires $\geq \log_2 k$ bits of side information (Theorem [\[thm:side-info\]](#thm:side-info){reference-type="ref" reference="thm:side-info"}). This is the paper's main quantitative IT statement and connects directly to decoder-side-information ideas.

**2. Exact-consistency characterization:** We define zero-incoherence capacity $C_0$ as the maximum encoding rate guaranteeing zero probability of location disagreement, and prove $C_0 = 1$ exactly (Theorem [\[thm:coherence-capacity\]](#thm:coherence-capacity){reference-type="ref" reference="thm:coherence-capacity"}). The proof is cast in explicit achievability/converse form.

**3. Multi-Terminal Interpretation:** We model encoding locations as terminals in a multi-terminal source coding problem. Derivation introduces perfect dependence, reducing effective rate. Only complete dependence on one source achieves zero incoherence.

**4. Rate-Complexity Tradeoffs:** We show that modification complexity is $O(1)$ at rate $1$ and $\Omega(n)$ above it. The gap is unbounded (Theorem [\[thm:unbounded-gap\]](#thm:unbounded-gap){reference-type="ref" reference="thm:unbounded-gap"}).

**5. Encoder Realizability:** Achieving capacity requires two encoder properties: causal propagation (analogous to feedback) and provenance observability (analogous to decoder side information). Both necessary; together sufficient (Theorem [\[thm:ssot-iff\]](#thm:ssot-iff){reference-type="ref" reference="thm:ssot-iff"}).

**Applications.** The abstract theory instantiates across domains. Sections [\[sec:evaluation\]](#sec:evaluation){reference-type="ref" reference="sec:evaluation"} and [\[sec:empirical\]](#sec:empirical){reference-type="ref" reference="sec:empirical"} provide short corollaries; the core theorems are domain-independent.

**Implications:**

1.  **For information theorists:** Zero-error ideas extend naturally to interactive multi-location encoding with modification constraints. The setting is nonclassical, but the side-information bound and achievability/converse threshold connect directly to established IT.

2.  **For coding theorists:** Derivation is the mechanism that introduces dependence and reduces effective encoding rate. The realizability theorem characterizes what system properties make that regime attainable.

3.  **For system designers:** If exact consistency is required, independent rate must be $\leq 1$. Systems operating above that threshold require external side information for resolution.

**Limitations:**

-   Results apply primarily to facts with modification constraints. Streaming data and high-frequency updates have different characteristics.

-   The complexity bounds are asymptotic. For small encoding systems (DOF $< 5$), the asymptotic gap is numerically small.

-   Application examples are brief and primarily computational. Richer non-software case studies are left to future work.

-   Realizability requirements focus on computational systems. Physical and biological encoding systems require separate analysis.

**Future Work:**

-   **Probabilistic coherence:** Extend to soft constraints where incoherence probability is bounded but non-zero, analogous to the transition from zero-error to vanishing-error capacity.

-   **Network encoding:** Study coherence capacity in networked encoding systems with communication constraints, connecting to network information theory.

-   **Rate-complexity extension:** Characterize the full rate-complexity function $R(M)$ beyond the sharp zero-error boundary analyzed here.

-   **Interactive capacity:** Study capacity under multi-round modification protocols, connecting to interactive information theory and directed information.

-   **Partial correlation:** Characterize coherence guarantees when derivation introduces partial (non-deterministic) correlation, extending beyond the perfect-correlation case.

## Artifacts {#sec:data-availability}

The Lean 4 formalization is included as supplementary material [@openhcsLeanProofs]. The OpenHCS case study and associated code references are provided for the worked instantiation (Section [\[sec:empirical\]](#sec:empirical){reference-type="ref" reference="sec:empirical"}).


# Mechanized Proofs (Lean 4) {#sec:lean .unnumbered}

Core theorem chains in this paper are machine-checked in Lean 4. The current build statistics are: **12818 lines across 60 files, 583 theorem/lemma statements, 0 `sorry` placeholders.**

## Mechanization Contract {#mechanization-contract .unnumbered}

Each theorem-level handle is typed as one of:

-   **Full:** direct Lean theorem support.

-   **Full (derived/model-level):** theorem-level closure by composition from mechanized cores in the stated model.

#### Finite zero-error information handles (fully mechanized).

-   UNQ1 (the `sideInfoBits` quantity realizing the paper's $\log_2 k$ expression)

-   UNQ1 (direct finite lower bound for side-information requirements)

-   UNQ1 (finite zero-error counting converse $K \le 2^L$)

-   UNQ1 (overflow contradiction bridge from counting converse)

-   OBS1 (exact recovery implies injectivity of the observation-plus-tag map)

-   OBS2 (injective observation-plus-tag maps admit exact decoders)

-   OBS3 (each observation fiber is bounded by the tag alphabet)

-   OBS4 (global observer/tag counting converse $|V|\le |O|\cdot |T|$)

-   OBS5 (confusability cliques require tag alphabets at least as large as the clique)

-   OBS6 (nontrivial cliques rule out observation-only exact recovery)

-   OBS7 (every exact-recovery architecture obeys a global support-count bound)

-   OBS8 (confusability cliques lower-bound formal architecture support count)

-   OBS9 (nontrivial cliques force architecture support count $>1$)

-   OBS10 (observation-only architectures are impossible on nontrivial cliques)

-   OBS11 (formal architecture support count is realized as a concrete 'Dof.dof' quantity)

-   OBS12 (nontrivial cliques force that concrete DOF strictly above one)

-   OBS13 (finite relaxed-error extension: any clique recovered exactly on a subset still obeys the tag lower bound)

-   PRB1 (exactly recovered state set has cardinality at most the observation/tag budget)

-   PRB2 (success probability is bounded by budget times a point-mass ceiling)

-   PRB3 (error probability lower bound from finite budget and point-mass ceiling)

-   PRB4 (elementary definition of vanishing error)

-   PRB5 (uniform positive error lower bound rules out vanishing error)

-   PRB6 (finite-family nonvanishing theorem under a uniform budget/mass gap)

-   PRB7 (uniform-source error lower bound from observation/tag budget)

-   PRB8 (uniform-source success probability is bounded by the observation/tag budget fraction)

-   PRB9 (weak-Fano-style budget lower bound for uniform finite sources)

-   PRB10 (uniform-source families with a budget-ratio gap cannot have vanishing error)

-   PRB11 (under the uniform source, success probability equals the exactly recovered fraction)

-   PRB12 (under the uniform source, error probability is one minus that fraction)

-   PRB13 (weak-Fano cardinality form: low error forces a large exactly recovered subset)

-   PRB14 (weak-Fano budget form recovered from the exact cardinality identity)

-   PRB15 (uniform-source success/failure partition entropy identity)

-   PRB16 (explicit finite Fano-style inequality for the uniform finite source)

-   PRB17 (observation-only specialization as a 'q'-ary entropy bound)

-   PRB18 (observation-only success probability is at most $1/K$ for the uniform source)

-   PRB19 (observation-only error probability is at least $1-1/K$ for the uniform source)

-   ENT2 (binary entropy is directly available from imported mathlib)

-   ENT3 (KL divergence self-equality theorem is directly available on PMF-derived measures)

-   ENT4 (PMF-level Bernoulli entropy agrees with mathlib's binary entropy)

-   ENT5 (Bernoulli PMF entropy is bounded by $\log 2$)

-   ENT6 (uniform PMF entropy on 'Fin(n+1)' equals $\log(n+1)$)

The source proof environment also now imports the current mathlib entropy/KL/PMF stack successfully via 'Ssot/EntropyGeneral.lean'. This does not yet yield a full general Fano theorem, but it confirms that a PMF-based entropy development can be built natively in the same source tree.

#### Graph/confusability handles (fully mechanized finite zero-error layer).

-   UNQ1 (proper coloring bounds clique size by alphabet size)

-   UNQ1 (complete confusability graph forces one tag per state)

-   UNQ1 (observation-fiber clique lower bound for zero-error tagging)

-   UNQ1 (constant-observation / maximal-barrier lower bound)

-   UNQ1 (worst-case observation-fiber lower bound)

-   UNQ1 (average observation-fiber occupancy lower bound)

-   UNQ1 (global counting converse $|V|\le|O|\cdot|T|$)

## Complete Claim Coverage Matrix {#complete-claim-coverage-matrix .unnumbered}

#### Foundations, capacity, and side-information chain.

-   `thm:oracle-arbitrary`: Full -- UNQ1.

-   `thm:dof-one-coherence`: Full -- UNQ1.

-   `thm:dof-gt-one-incoherence`: Full -- UNQ1.

-   `cor:coherence-forces-ssot`: Full -- UNQ1.

-   `thm:correctness-forcing`: Full -- UNQ1.

-   `thm:dof-inconsistency`: Full -- UNQ1.

-   `cor:dof-risk`: Full -- UNQ1.

-   `thm:dof-optimal`: Full -- UNQ1, UNQ1.

-   `thm:cap-encoding`: Full -- UNQ1.

-   `thm:static-flp`: Full -- UNQ1.

-   `thm:redundancy-incoherence`: Full -- UNQ1.

-   `thm:coherence-capacity`: Full -- UNQ1.

-   `thm:capacity-achievability`: Full -- UNQ1.

-   `thm:capacity-converse`: Full -- UNQ1.

-   `cor:capacity-unique`: Full -- L1.

-   `cor:redundancy-above`: Full -- UNQ1.

-   `thm:rate-incoherence-step`: Full -- UNQ1.

-   `thm:design-necessity`: Full -- UNQ1.

-   `cor:architectural-forcing`: Full -- L1, UNQ1.

-   `thm:incoherence-graph`: Full (derived/model-level) -- UNQ1, UNQ1.

-   `thm:side-info`: Full -- UNQ1.

-   `cor:dof1-zero-side`: Full -- UNQ1.

-   `cor:side-info-redundancy`: Full -- UNQ1.

-   `cor:multi-terminal`: Full (derived/model-level) -- UNQ1, UNQ1.

-   `thm:fano-converse`: Full (finite zero-error counting form) -- UNQ1.

-   `lem:info-dof`: Full (finite counting contradiction form) -- UNQ1.

#### Derivation and realizability chain.

-   `thm:derivation-lattice`: Full (model-level) -- UNQ1.

-   `thm:dof-antimonotone`: Full (model-level) -- UNQ1, UNQ1.

-   `cor:minimal-dof1`: Full (model-level) -- UNQ1, UNQ1.

-   `thm:dof-complexity`: Full (model-level) -- UNQ1.

-   `thm:ssot-determinate`: Full -- UNQ1.

-   `thm:ssot-optimal`: Full -- UNQ1.

-   `thm:ssot-unique`: Full -- L1.

-   `cor:no-redundancy`: Full -- UNQ1.

-   `thm:derivation-excludes`: Full -- UNQ1.

-   `cor:metaprogramming`: Full (derived/model-level) -- UNQ1, UNQ1.

-   `lem:confusability-clique`: Full (finite zero-error graph layer) -- UNQ1, UNQ1, UNQ1, UNQ1, UNQ1.

-   `thm:timing-forces`: Full -- UNQ1.

-   `thm:causal-necessary`: Full -- UNQ1.

-   `thm:provenance-necessary`: Full -- UNQ1.

-   `thm:independence`: Full -- UNQ1, UNQ1.

-   `thm:ssot-iff`: Full -- UNQ1.

-   `thm:generated-second`: Full -- UNQ1.

-   `cor:lang-realizability`: Full -- UNQ1.

#### Bounds, regimes, and optimization chain.

-   `thm:upper-bound`: Full -- UNQ1.

-   `thm:lower-bound`: Full -- UNQ1.

-   `thm:unbounded-gap`: Full -- UNQ1.

-   `cor:arbitrary-reduction`: Full -- UNQ1.

-   `thm:operating-regimes`: Full -- UNQ1.

-   `thm:pareto-optimal`: Full -- UNQ1.

-   `cor:no-tradeoff`: Full -- UNQ1.

-   `thm:amortized`: Full -- UNQ1.

## Verification Instructions {#verification-instructions .unnumbered}

1.  Lean-only verification (recommended): `cd docs/papers/paper2_ssot/proofs && lake build`

2.  Direct Lean build: `python3 scripts/build_papers.py lean paper2_it`

## Scope Note {#scope-note .unnumbered}

The current source proof tree is axiom-free with respect to the paper-specific information-theoretic closure layer: the side-information and counting-converse handles are discharged by finite zero-error arguments rather than paper-local assumption bundles.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper2_ssot/proofs/`
- Lines: 12818
- Theorems: 583
- `sorry` placeholders: 0
