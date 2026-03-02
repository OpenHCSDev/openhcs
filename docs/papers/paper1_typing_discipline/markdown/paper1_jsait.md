# Paper: Identification Capacity and Rate-Query Tradeoffs in Classification Systems

**Status**: JSAIT-ready | **Lean**: 7215 lines, 306 theorems

---

## Abstract

We study zero-error class identification under constrained observations with three resources: tag rate $L$ (bits per entity), identification cost $W$ (attribute queries), and distortion $D$ (misidentification probability). We prove an information barrier: if the attribute-profile map $\pi$ is not injective on classes, then attribute-only observation cannot identify class identity with zero error. Let $A_\pi := \max_u |\{c : \pi(c)=u\}|$ be collision multiplicity. Any $D=0$ scheme must satisfy $L \ge \log_2 A_\pi$, and this bound is tight. In maximal-barrier domains ($A_\pi=k$), the nominal point $(L,W,D)=(\lceil\log_2 k\rceil,O(1),0)$ is the unique Pareto-optimal zero-error point. Without tags ($L=0$), zero-error identification requires $W=\Omega(d)$ queries, where $d$ is the distinguishing dimension (worst case $d=n$, so $W=\Omega(n)$). Minimal sufficient query sets form the bases of a matroid, making $d$ well-defined and linking the model to zero-error source coding via graph entropy. We also state fixed-axis incompleteness: a fixed observation axis is complete only for axis-measurable properties. Results instantiate to databases, biology, typed software systems, and model registries, and are machine-checked in Lean 4 (7215 lines, 306 theorem/lemma statements, 0 `sorry`).

**Keywords:** rate-distortion theory, identification capacity, zero-error source coding, query complexity, matroid structure, classification systems


## The Identification Problem

Consider an encoder-decoder pair communicating about entities from a large universe $\mathcal{V}$. The decoder must *identify* each entity, determining which of $k$ classes it belongs to, using only:

-   A *tag* of $L$ bits stored with the entity, and/or

-   *Queries* to a binary oracle: "does entity $v$ satisfy attribute $I$?"

This is not reconstruction (the decoder need not recover $v$), but *identification* in the sense of Ahlswede and Dueck [@ahlswede1989identification]: the decoder must answer "which class?" with zero or bounded error. Our work extends this framework to consider the tradeoff between tag storage, query complexity, and identification accuracy.

We prove three results:

1.  **Information barrier (identifiability limit).** When the attribute profile $\pi: \mathcal{V} \to \{0,1\}^n$ is not injective on classes, zero-error identification via queries alone is impossible: any decoder produces identical output on colliding classes, so cannot be correct for both.

2.  **Optimal tagging (achievability).** A tag of $L = \lceil \log_2 k \rceil$ bits achieves zero-error identification with $W = O(1)$ query cost. For maximal-barrier domains ($A_\pi = k$), this is the unique Pareto-optimal point in the $(L, W, D)$ tradeoff space at $D=0$; in general domains, the converse depends on $A_\pi := \max_u |\{c : \pi(c)=u\}|$.

3.  **Matroid structure (query complexity).** Minimal sufficient query sets form the bases of a matroid. The *distinguishing dimension* (the common cardinality of all minimal sets) is well-defined and lower-bounds the query cost $W$ for any tag-free scheme.

These results are universal: the theory applies to type systems, databases, biological taxonomy, and knowledge graphs. We develop the mathematics in full generality, then exhibit concrete instantiations.

## The Observation Model

We formalize the observational constraint as a family of binary predicates. The terminology is deliberately abstract; concrete instantiations follow in Section [\[sec:applications\]](#sec:applications){reference-type="ref" reference="sec:applications"}.

::: definition
Let $\mathcal{V}$ be a set of entities (program objects, database records, biological specimens, library items). Let $\mathcal{I}$ be a finite set of binary *attributes*. Each $I \in \mathcal{I}$ induces a bipartition of $\mathcal{V}$ via $q_I$, and the full family induces the observational equivalence partition.
:::

::: remark
We use "attribute" for the abstract concept. In type systems, attributes are *interfaces* or *method signatures*. In databases, they are *columns*. In taxonomy, they are *phenotypic characters*. In library science, they are *facets*. The mathematics is identical.
:::

::: definition
For each $I \in \mathcal{I}$, define the attribute-membership observation $q_I: \mathcal{V} \to \{0,1\}$: $$q_I(v) = \begin{cases} 1 & \text{if } v \text{ satisfies attribute } I \\ 0 & \text{otherwise} \end{cases}$$ Let $\Phi_{\mathcal{I}} = \{q_I : I \in \mathcal{I}\}$ denote the attribute observation family.
:::

::: remark
We write $n := |\mathcal{I}|$ for the ambient number of available attributes. We write $d$ for the distinguishing dimension (the common size of all minimal distinguishing query sets; Definition [\[def:distinguishing-dimension\]](#def:distinguishing-dimension){reference-type="ref" reference="def:distinguishing-dimension"}), so $d \le n$ and there exist worst-case families with $d = n$. We write $m$ for the number of *query sites* (call sites) that perform attribute checks in a program or protocol (used only in the complexity-of-maintenance discussion). When discussing a particular identification/verification task, we may write $s$ for the number of attributes actually queried/traversed by the procedure (e.g., members/fields checked in a structural type test, phenotypic characters checked in taxonomy), with $s \le n$. The maintenance-only parameter $m$ appears only in Section [\[sec:complexity\]](#sec:complexity){reference-type="ref" reference="sec:complexity"}.
:::

::: definition
The attribute profile function $\pi: \mathcal{V} \to \{0,1\}^{|\mathcal{I}|}$ maps each value to its complete attribute signature: $$\pi(v) = (q_I(v))_{I \in \mathcal{I}}$$
:::

::: definition
Values $v, w \in \mathcal{V}$ are *attribute-indistinguishable*, written $v \sim w$, iff $\pi(v) = \pi(w)$.
:::

The relation $\sim$ is an equivalence relation. We write $[v]_\sim$ for the equivalence class of $v$.

::: definition
An *attribute-only observer* is any procedure whose interaction with a value $v \in \mathcal{V}$ is limited to queries in $\Phi_{\mathcal{I}}$. Formally, the observer interacts with $v$ only via primitive attribute queries $q_I \in \Phi_{\mathcal{I}}$; hence any transcript (and output) factors through $\pi(v)$.
:::

## The Central Question

The central question is: **what semantic properties can an attribute-only observer compute?**

A semantic property is a function $P: \mathcal{V} \to \{0,1\}$ (or more generally, $P: \mathcal{V} \to Y$ for some codomain $Y$). We say $P$ is *attribute-computable* if there exists a function $f: \{0,1\}^{|\mathcal{I}|} \to Y$ such that $P(v) = f(\pi(v))$ for all $v$.

## The Information Barrier

::: theorem
[]{#thm:information-barrier label="thm:information-barrier"} Let $P: \mathcal{V} \to Y$ be any function. If $P$ is attribute-computable, then $P$ is constant on $\sim$-equivalence classes: $$v \sim w \implies P(v) = P(w)$$ Equivalently: no attribute-only observer can compute any property that varies within an equivalence class.
:::

::: proof
*Proof.* Suppose $P$ is attribute-computable via $f$, i.e., $P(v) = f(\pi(v))$ for all $v$. Let $v \sim w$, so $\pi(v) = \pi(w)$. Then: $$P(v) = f(\pi(v)) = f(\pi(w)) = P(w)$$ ◻
:::

::: remark
The barrier is *informational*, not computational. Given unlimited time, memory, and computational power, an attribute-only observer still cannot distinguish $v$ from $w$ when $\pi(v) = \pi(w)$. The constraint is on the evidence itself.
:::

::: remark
Theorem [\[thm:information-barrier\]](#thm:information-barrier){reference-type="ref" reference="thm:information-barrier"} is the foundational invariance statement. The technical contribution is the downstream structure built on top of it: the ambiguity-based converse (Theorem [\[thm:converse\]](#thm:converse){reference-type="ref" reference="thm:converse"}), the Pareto characterization (Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"}), and the matroid/equicardinality results (Section [\[sec:matroid\]](#sec:matroid){reference-type="ref" reference="sec:matroid"}).
:::

::: corollary
[]{#cor:provenance-barrier label="cor:provenance-barrier"} Let $C: \mathcal{V} \to \{1,\ldots,k\}$ be the class assignment function. If there exist values $v, w$ with $\pi(v) = \pi(w)$ but $C(v) \neq C(w)$, then class identity is not attribute-computable.
:::

::: proof
*Proof.* Direct application of Theorem [\[thm:information-barrier\]](#thm:information-barrier){reference-type="ref" reference="thm:information-barrier"} to $P = C$. ◻
:::

## The Positive Result: Nominal Tagging

We now show that augmenting attribute observations with a single primitive, nominal-tag access, achieves constant witness cost.

::: definition
A *nominal tag* is a value $\tau(v) \in \mathcal{T}$ associated with each $v \in \mathcal{V}$, representing the class identity of $v$. The *nominal-tag access* operation returns $\tau(v)$ in $O(1)$ time.
:::

::: definition
The extended primitive query set is $\Phi_{\mathcal{I}}^+ = \Phi_{\mathcal{I}} \cup \{\tau\}$, where $\tau$ denotes nominal-tag access.
:::

::: definition
Let $W(P)$ denote the minimum number of primitive queries from $\Phi_{\mathcal{I}}^+$ required to compute property $P$. We distinguish two tasks:

-   $W_{\text{id}}$: Cost to identify the class of a single entity.

-   $W_{\text{eq}}$: Cost to determine if two entities have the same class.

Unless specified, $W$ refers to $W_{\text{eq}}$.
:::

::: theorem
[]{#thm:constant-witness label="thm:constant-witness"} Under nominal-tag access, class identity checking has constant witness cost: $$W(\text{class-identity}) = O(1)$$ Specifically, the witness procedure is: return $\tau(v_1) = \tau(v_2)$.
:::

::: proof
*Proof.* The procedure makes exactly 2 primitive queries (one $\tau$ access per value) and one comparison. This is $O(1)$ regardless of the number of available attributes $|\mathcal{I}|$. ◻
:::

::: theorem
[]{#thm:interface-lower-bound label="thm:interface-lower-bound"} For attribute-only observers, class identity checking requires: $$W(\text{class-identity}) = \Omega(d)$$ in the worst case, where $d$ is the distinguishing dimension (Definition [\[def:distinguishing-dimension\]](#def:distinguishing-dimension){reference-type="ref" reference="def:distinguishing-dimension"}).
:::

::: proof
*Proof.* Assume a zero-error attribute-only procedure halts after fewer than $d$ queries on every execution path. Fix any execution path and let $Q \subseteq \mathcal{I}$ be the set of queried attributes on that path, so $|Q|<d$. Since $d$ is the cardinality of every minimal distinguishing set, no set of size $<d$ is distinguishing; hence there exist values $v,w$ from different classes with identical answers on all attributes in $Q$.

An adversary can answer the procedure's queries consistently with both $v$ and $w$ along this path. Therefore the resulting transcript (and output) is identical on $v$ and $w$, contradicting zero-error class identification. So some execution path must use at least $d$ queries, giving worst-case cost $\Omega(d)$. ◻
:::

## Main Contributions

This paper establishes the following results:

1.  **Information Barrier Theorem** (Theorem [\[thm:information-barrier\]](#thm:information-barrier){reference-type="ref" reference="thm:information-barrier"}): Attribute-only observers cannot compute any property that varies within $\sim$-equivalence classes. This is an information-theoretic impossibility, not a computational limitation.

2.  **Constant-Witness Theorem** (Theorem [\[thm:constant-witness\]](#thm:constant-witness){reference-type="ref" reference="thm:constant-witness"}): Nominal-tag access achieves $W(\text{class-identity}) = O(1)$, with matching lower bound $\Omega(d)$ for attribute-only observers (Theorem [\[thm:interface-lower-bound\]](#thm:interface-lower-bound){reference-type="ref" reference="thm:interface-lower-bound"}), where $d$ is the distinguishing dimension (Definition [\[def:distinguishing-dimension\]](#def:distinguishing-dimension){reference-type="ref" reference="def:distinguishing-dimension"}).

3.  **Complexity Separation** (Section [\[sec:complexity\]](#sec:complexity){reference-type="ref" reference="sec:complexity"}): We establish O(1) vs O(k) vs $\Omega(d)$ complexity bounds for error localization under different observation regimes (where $d$ is the distinguishing dimension).

4.  **Matroid Structure** (Section [\[sec:matroid\]](#sec:matroid){reference-type="ref" reference="sec:matroid"}): Minimal distinguishing query sets form the bases of a matroid. All such sets have equal cardinality, establishing a well-defined "distinguishing dimension."

5.  **$(L, W, D)$ Optimality** (Section [\[sec:lwd\]](#sec:lwd){reference-type="ref" reference="sec:lwd"}): We characterize the zero-error converse via collision multiplicity $A_\pi$ and prove uniqueness of the nominal point in the maximal-barrier regime ($A_\pi=k$).

6.  **Machine-Checked Proofs**: All results formalized in Lean 4 (7215 lines, 306 theorem/lemma statements, 0 `sorry` placeholders).

## Related Work and Positioning

**Identification via channels.** Our work extends the identification paradigm introduced by Ahlswede and Dueck [@ahlswede1989identification; @ahlswede1989identification2]. In their framework, a decoder need not reconstruct a message but only answer "is the message $m$?" for a given hypothesis. This yields dramatically different capacity: double-exponential codebook sizes become achievable. Our setting differs in three ways: (1) we consider zero-error identification rather than vanishing error, (2) queries are adaptive rather than block codes, and (3) we allow auxiliary tagging (rate $L$) to reduce query cost. The $(L, W, D)$ tradeoff generalizes Ahlswede-Dueck to a multi-dimensional operating regime.

**Rate-distortion theory.** The $(L, W, D)$ framework connects to Shannon's rate-distortion theory [@shannon1959coding; @berger1971rate] with an important twist: the "distortion" $D$ is semantic (class misidentification), and there is a second resource $W$ (query cost) alongside rate $L$. Classical rate-distortion asks: what is the minimum rate to achieve distortion $D$? We ask: given rate $L$, what is the minimum query cost $W$ to achieve distortion $D = 0$? Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"} gives the converse in terms of collision multiplicity and identifies the unique nominal point in the maximal-barrier regime.

**Rate-distortion-perception tradeoffs.** Blau and Michaeli [@blau2019rethinking] extended rate-distortion theory by adding a perception constraint, creating a three-way tradeoff. Our query cost $W$ plays an analogous role: it measures the interactive cost of achieving low distortion rather than a distributional constraint. This parallel suggests that $(L, W, D)$ tradeoffs may admit similar geometric characterizations. Section [\[sec:extensions\]](#sec:extensions){reference-type="ref" reference="sec:extensions"} develops this connection further.

**Zero-error information theory.** The matroid structure (Section [\[sec:matroid\]](#sec:matroid){reference-type="ref" reference="sec:matroid"}) connects to zero-error capacity and graph entropy. Körner [@korner1973coding] and Witsenhausen [@witsenhausen1976zero] studied zero-error source coding where confusable symbols must be distinguished. Our distinguishing dimension (Definition [\[def:distinguishing-dimension\]](#def:distinguishing-dimension){reference-type="ref" reference="def:distinguishing-dimension"}) is the minimum number of binary queries to separate all classes, which is precisely the zero-error identification cost when $L = 0$.

**Query complexity and communication complexity.** The $\Omega(d)$ lower bound for attribute-only identification relates to decision tree complexity [@buhrman2002complexity] and interactive communication [@orlitsky1991worst]. The key distinction is that our queries are constrained to a fixed observable family $\mathcal{I}$, not arbitrary predicates.

**Compression in classification systems.** The framework applies uniformly to databases, knowledge graphs, taxonomy, and typed software systems: for zero-error identification, ambiguity induces a minimum metadata requirement $L \ge \log_2 A_\pi$ (Theorem [\[thm:converse\]](#thm:converse){reference-type="ref" reference="thm:converse"}), with maximal-barrier specialization $L \ge \log_2 k$.

**Programming-language corollary (secondary).** In nominal-vs-structural typing settings [@Cardelli1985; @cook1990inheritance], the model yields a concrete cost statement: under attribute collisions, purely structural identification has worst-case $\Omega(d)$ witness cost, while nominal tags achieve $O(1)$ identification using $O(\log A_\pi)$ bits. This is the paper's PL-facing corollary; the main contribution remains the information-theoretic characterization.

## Paper Organization

Section [\[sec:framework\]](#sec:framework){reference-type="ref" reference="sec:framework"} formalizes the compression framework and defines the $(L, W, D)$ tradeoff. Section [\[sec:complexity\]](#sec:complexity){reference-type="ref" reference="sec:complexity"} establishes complexity bounds for error localization. Section [\[sec:matroid\]](#sec:matroid){reference-type="ref" reference="sec:matroid"} proves the matroid structure of distinguishing query families. Section [\[sec:witness\]](#sec:witness){reference-type="ref" reference="sec:witness"} analyzes witness cost in detail. Section [\[sec:lwd\]](#sec:lwd){reference-type="ref" reference="sec:lwd"} proves the ambiguity-based converse and Pareto characterization. Section [\[sec:applications\]](#sec:applications){reference-type="ref" reference="sec:applications"} provides cross-domain instantiations as secondary illustrations. Section [\[sec:conclusion\]](#sec:conclusion){reference-type="ref" reference="sec:conclusion"} concludes. Appendix [\[sec:lean\]](#sec:lean){reference-type="ref" reference="sec:lean"} describes the Lean 4 formalization.


_Failed to convert 02_compression_framework.tex_

## The Error Localization Theorem

#### Scope of this section.

This section studies *maintenance/localization* complexity, measured by locations to inspect ($E(\cdot)$), not per-instance identification complexity ($W$) from Sections [\[sec:framework\]](#sec:framework){reference-type="ref" reference="sec:framework"} and [\[sec:witness\]](#sec:witness){reference-type="ref" reference="sec:witness"}. The metrics are related but distinct: $W$ quantifies online class-identification effort, while $E$ quantifies where constraint logic is distributed in implementations.

::: definition
Let $E(\mathcal{O})$ be the number of locations that must be inspected to find all potential violations of a constraint under observation family $\mathcal{O}$.
:::

::: theorem
[]{#thm:nominal-localization label="thm:nominal-localization"} $E(\text{nominal-tag}) = O(1)$.
:::

::: proof
*Proof.* Under nominal-tag observation, the constraint "$v$ must be of class $A$" is satisfied iff $\tau(v) \in \text{subtypes}(A)$. This is determined at a single location: the definition of $\tau(v)$'s class. One location. ◻
:::

::: theorem
[]{#thm:declared-localization label="thm:declared-localization"} $E(\text{attribute-only, declared}) = O(k)$ where $k$ = number of entity classes.
:::

::: proof
*Proof.* With declared attribute sets (interfaces in the PL instantiation), the constraint "$v$ must satisfy attribute $I$" requires verifying that each class satisfies all attributes in $I$. For $k$ classes, $O(k)$ locations. ◻
:::

::: theorem
[]{#thm:attribute-localization label="thm:attribute-localization"} $E(\text{attribute-only}) = \Omega(m)$ where $m$ = number of query sites.
:::

::: proof
*Proof.* Under attribute-only observation, each query site independently checks "does $v$ have attribute $a$?" with no centralized declaration. For $m$ query sites, each must be inspected. Lower bound is $\Omega(m)$. ◻
:::

::: corollary
[]{#cor:strict-dominance label="cor:strict-dominance"} Nominal-tag observation strictly dominates attribute-only: $E(\text{nominal-tag}) = O(1) < \Omega(m) = E(\text{attribute-only})$ for all $m > 1$.
:::

## The Information Scattering Theorem

::: definition
Let $I(\mathcal{O}, c)$ be the set of locations where constraint $c$ is encoded under observation family $\mathcal{O}$.
:::

::: theorem
[]{#thm:attribute-scattering label="thm:attribute-scattering"} For attribute-only observation, $|I(\text{attribute-only}, c)| = O(m)$ where $m$ = query sites using constraint $c$.
:::

::: proof
*Proof.* Each attribute query independently encodes the constraint. No shared reference exists. Constraint encodings scale with query sites. ◻
:::

::: theorem
[]{#thm:nominal-centralization label="thm:nominal-centralization"} For nominal-tag observation, $|I(\text{nominal-tag}, c)| = O(1)$.
:::

::: proof
*Proof.* The constraint "must be of class $A$" is encoded once in the definition of $A$. All tag checks reference this single definition. ◻
:::

::: corollary
[]{#cor:maintenance-entropy label="cor:maintenance-entropy"} Attribute-only observation maximizes maintenance entropy; nominal-tag observation minimizes it.
:::


_Failed to convert 03_matroid_structure.tex_

_Failed to convert 04_kolmogorov_witness.tex_

_Failed to convert 05_rate_distortion.tex_

The preceding sections established abstract information-theoretic results (Sections [\[sec:framework\]](#sec:framework){reference-type="ref" reference="sec:framework"}--[\[sec:lwd\]](#sec:lwd){reference-type="ref" reference="sec:lwd"}). This section provides secondary cross-domain illustrations. The mathematics is unchanged by domain; these examples only instantiate the same observer-model primitives.

## Biological Taxonomy: Phenotype vs Genotype

Linnean taxonomy classifies organisms by observable phenotypic characters: morphology, behavior, habitat. This is attribute-only observation. The information barrier applies: phenotypically identical organisms from distinct species are indistinguishable.

**The cryptic species problem:** Cryptic species share identical phenotypic profiles but are reproductively isolated and genetically distinct. Attribute-only observation (morphology) cannot distinguish them: $\pi(A) = \pi(B)$ but $\text{species}(A) \neq \text{species}(B)$.

**The nominal tag:** DNA barcoding provides the resolution [@DNABarcoding]. A short genetic sequence (e.g., mitochondrial COI) acts as the nominal tag: $O(1)$ identity verification via sequence comparison. This reduced cryptic species identification from $\Omega(s)$ phenotypic examination (checking $s$ characters) to constant-time molecular lookup.

## Library Classification: Subject vs ISBN

Library classification systems like Dewey Decimal observe subject matter, a form of attribute-only classification. Two books on the same subject are indistinguishable by subject code alone.

**The nominal tag:** The ISBN (International Standard Book Number) is the nominal tag [@ISBN]. Given two physical books, identity verification is $O(1)$: compare ISBNs. Without ISBNs, distinguishing two copies of different editions on the same subject requires $O(s)$ attribute inspection (publication date, page count, publisher, etc.).

## Database Systems: Columns vs Primary Keys

In big-data systems, relational databases observe entities via column values. The information barrier applies: rows with identical column values, excluding the key, are indistinguishable.

**The nominal tag:** The primary key is the nominal tag [@Codd1990]. Entity identity is $O(1)$: compare keys. This is why database theory requires keys---without them, the system cannot answer "is this the same entity?"

**Natural vs surrogate keys:** Natural keys (composed of attributes) are attribute-only observation and inherit its limitations. Surrogate keys (auto-increment IDs, UUIDs) are pure nominal tags: no semantic content, pure identity.

## Programming-Language Snapshot (Secondary Illustration)

Programming-language runtimes are one instantiation of the same abstraction, not the source of the theory. Table [1](#tab:pl-snapshot){reference-type="ref" reference="tab:pl-snapshot"} summarizes the mapping from runtime mechanisms to $(L,W,D)$ model primitives.

::: {#tab:pl-snapshot}
  **Runtime**   **Nominal mechanism**                                               **Identity cost**
  ------------- ------------------------------------------------------------------ -------------------
  CPython       `ob_type` / `type(a) is type(b)` [@CPythonDocs]                          $O(1)$
  Java          class tag via `.getClass()` / `instanceof` [@JVMSpec; @JavaDocs]    $O(1)$ to $O(d)$
  TypeScript    structural compatibility only [@TypeScriptDocs]                          $O(s)$
  Rust          `TypeId` for nominal identity [@RustDocs]                                $O(1)$

  : Programming-language snapshot as a secondary illustration of the abstract observer model.
:::

Without a class tag, identity checks are structural and scale with inspected structure size ($O(s)$). With a class tag, identity is constant-time (or near-constant with bounded hierarchy traversal). This is exactly the generic witness-cost separation from Sections [\[sec:witness\]](#sec:witness){reference-type="ref" reference="sec:witness"} and [\[sec:lwd\]](#sec:lwd){reference-type="ref" reference="sec:lwd"}.

## Cross-Domain Summary

  **Domain**      **Attribute-Only**          **Nominal Tag**      **$W$**
  --------------- --------------------------- ------------------- ---------
  Biology         Phenotype (morphology)      DNA barcode (COI)    $O(1)$
  Libraries       Subject (Dewey)             ISBN                 $O(1)$
  Databases       Column values               Primary key          $O(1)$
  CPython         `hasattr` probing           `ob_type` pointer    $O(1)$
  Java            Attribute/interface check   `.getClass()`        $O(1)$
  TypeScript      Structural check            (none at runtime)    $O(s)$
  Rust (static)   Trait bounds                `TypeId`             $O(1)$

  : Witness cost for identity across classification systems. Nominal tags achieve $O(1)$; attribute-only pays $O(s)$ per structural check (or $O(k)$ when enumerating classes under declared attribute catalogs, e.g., interfaces in PL runtimes).

The pattern is universal: systems with nominal tags achieve $O(1)$ witness cost; systems without them pay $O(s)$ or $O(k)$. This is not domain-specific; it is the information barrier theorem instantiated across classification systems.

## Machine Learning: Model Identification and Versioning

Neural network models in production systems face the identification problem: given two model instances, determine if they represent the same architecture. Model registries must compress model metadata while enabling efficient identification.

**Attribute-only approach:** Compare architecture fingerprints (layer counts, activation functions, parameter counts, connectivity patterns). Cost: $O(s)$ where $s$ is the number of architectural features.

**Nominal tag:** Model hash (e.g., SHA-256 of architecture definition) or registry ID. Cost: $O(1)$.

The $(L, W, D)$ tradeoff applies directly: storing $\lceil \log_2 k \rceil$ bits per model (where $k$ is the number of distinct architectures in the registry) enables $O(1)$ identification with $D = 0$. Attribute-based versioning requires $\Omega(d)$ feature comparisons and risks false positives ($D > 0$) when architectures share identical fingerprints but differ in subtle structural details.

**Example:** A model registry with $k = 10^6$ architectures requires only 20 bits per model for perfect identification via nominal tags, versus $O(d)$ queries over potentially hundreds of architectural features for attribute-based approaches.


## Noisy Query Model

Throughout this paper, queries are deterministic: $q_I(v) \in \{0,1\}$ is a fixed function of $v$. In practice, observations may be corrupted. We sketch an extension to noisy queries and state the resulting open problems.

::: definition
A *noisy observation channel* with crossover probability $\epsilon \in [0, 1/2)$ returns: $$\tilde{q}_I(v) = \begin{cases}
q_I(v) & \text{with probability } 1 - \epsilon \\
1 - q_I(v) & \text{with probability } \epsilon
\end{cases}$$ Each query response is an independent BSC$(\epsilon)$ corruption of the true value.
:::

::: definition
The *$\epsilon$-noisy identification capacity* is the supremum rate (in bits per entity) at which zero-error identification is achievable when all attribute queries pass through a BSC$(\epsilon)$.
:::

In the noiseless case ($\epsilon = 0$), Theorem [\[thm:identification-capacity\]](#thm:identification-capacity){reference-type="ref" reference="thm:identification-capacity"} shows the capacity is binary: $\log_2 k$ if $\pi$ is class-injective, $0$ otherwise. For $\epsilon > 0$, several questions arise.

**Open problem (noisy identification cost).** For $\epsilon > 0$ and class-injective $\pi$, zero-error identification is impossible with finite queries (since BSC has nonzero error probability). With bounded error $\delta > 0$, we expect the identification cost to scale as $W = \Theta\left(\frac{\log(1/\delta)}{(1 - 2\epsilon)^2}\right)$ queries per entity. A key observation is that a nominal tag of $L \geq \lceil \log_2 k \rceil$ bits (transmitted noiselessly) should restore $O(1)$ identification regardless of query noise.

The third point is the key insight: *nominal tags provide a noise-free side channel*. Even when attribute observations are corrupted, a clean tag enables $O(1)$ identification. This strengthens the case for nominal tagging in noisy environments, precisely the regime where "duck typing" would require many repeated queries to achieve confidence.

**Connection to identification via channels.** The noisy model connects more directly to Ahlswede-Dueck identification [@ahlswede1989identification]. In their framework, identification capacity over a noisy channel can exceed Shannon capacity (double-exponential codebook sizes). Our setting differs: we have *adaptive queries* rather than block codes, and the decoder must identify a *class* rather than test a hypothesis. Characterizing the interplay between adaptive query strategies and channel noise is an open problem.

## Rate-Distortion-Query Tradeoff Surface

The $(L, W, D)$ tradeoff admits a natural geometric interpretation. In the maximal-barrier regime we identify a unique Pareto-optimal point at $D = 0$ (Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"}); outside that regime, the full tradeoff surface can contain multiple $D=0$ frontier points.

**Fixed-$W$ slices.** For fixed query budget $W$, what is the minimum tag rate $L$ to achieve distortion $D$? When $W \geq d$ (the distinguishing dimension), zero distortion is achievable with $L = 0$ via exhaustive querying. When $W < d$, the observer cannot distinguish all classes, and either:

-   Accept $D > 0$ (misidentification), or

-   Add tags ($L > 0$) to compensate for insufficient queries.

**Fixed-$L$ slices.** For fixed tag rate $L < \log_2 k$, the tag partitions the $k$ classes into $2^L$ groups. Within each group, the observer must use queries to distinguish. The query cost is determined by the distinguishing dimension *within each group*, which is potentially much smaller than the global dimension.

**Open problem (subadditivity of query cost).** For a tag of rate $L$ partitioning classes into groups $G_1, \ldots, G_{2^L}$, we expect $W(L) \leq \max_i d(G_i)$, where $d(G_i)$ is the distinguishing dimension within group $G_i$. Optimal tag design should minimize this maximum. Characterizing the optimal partition remains open.

## Semantic Distortion Measures

We have treated distortion $D$ as binary (correct identification or not). Richer distortion measures are possible:

-   **Hierarchical distortion**: Misidentifying a class within the same genus (biological) or module (type system) is less severe than cross-genus errors.

-   **Weighted distortion**: Some misidentifications have higher cost than others (e.g., type errors causing security vulnerabilities vs. benign type confusion).

## Privacy and Security

**Privacy-preserving identification.** Nominal tags enable zero-knowledge proofs of class membership without revealing attribute profiles. An entity can prove \"I belong to class $C$\" by revealing $\tau(v) = C$ without exposing $\pi(v)$, preserving attribute privacy. Attribute-only schemes must reveal the complete profile $\pi(v)$ to prove membership, leaking structural information.

**Secure model verification.** In machine learning deployment, compressed model identifiers prevent model substitution attacks. Verifying model identity via nominal tags ($O(1)$ hash comparison) is more efficient and secure than attribute-based verification ($O(s)$ architecture inspection), which is vulnerable to adversarial perturbations that preserve structural fingerprints while altering behavior.

## Connection to Rate-Distortion-Perception Theory

Blau and Michaeli [@blau2019rethinking] extended classical rate-distortion theory by adding a *perception* constraint: the reconstructed distribution must match a target distribution under some divergence measure. This creates a three-way tradeoff between rate, distortion, and perceptual quality.

Our $(L, W, D)$ framework admits a parallel interpretation. The query cost $W$ plays a role analogous to the perception constraint: it measures the *interactive cost* of achieving low distortion, rather than a distributional constraint. Just as rate-distortion-perception theory asks "what is the minimum rate to achieve distortion $D$ while satisfying perception constraint $P$?", we ask "what is the minimum tag rate $L$ to achieve distortion $D$ with query budget $W$?"

The analogy suggests several directions:

-   **Perception as identification fidelity**: In classification systems that must preserve statistical properties (e.g., sampling from a type distribution), a perception constraint would require the observer's class estimates to have the correct marginal distribution, not just low expected error.

-   **Three-resource tradeoffs**: The $(L, W, D)$ Pareto frontier (Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"}) is a discrete analogue of the rate-distortion-perception tradeoff surface. Characterizing this surface for specific classification problems would extend the geometric rate-distortion program to identification settings.

Formalizing these connections would unify identification capacity with the broader rate-distortion-perception literature.


This paper presents an information-theoretic analysis of classification under observational constraints. We prove three main results:

1.  **Information Barrier**: Observers limited to attribute-membership queries cannot compute properties that vary within indistinguishability classes. This is universal: it applies to biological taxonomy, database systems, library classification, and programming language runtimes alike.

2.  **Witness Optimality**: Nominal-tag observers achieve $W(\text{identity}) = O(1)$, the minimum witness cost. The gap from attribute-only observation ($\Omega(d)$, with a worst-case family where $d = n$) is unbounded.

3.  **Matroid Structure**: Minimal distinguishing query sets form the bases of a matroid. The distinguishing dimension of a classification problem is well-defined and computable.

## The Universal Pattern

Across domains, the same structure recurs:

-   **Biology**: Phenotypic observation cannot distinguish cryptic species. DNA barcoding (nominal tag) resolves them in $O(1)$.

-   **Databases**: Column-value queries cannot distinguish rows with identical attributes. Primary keys (nominal tag) provide $O(1)$ identity.

-   **Type systems**: Attribute observation (interfaces/method signatures in this instantiation) cannot distinguish structurally identical types. Type tags provide $O(1)$ identity.

The information barrier is not a quirk of any particular domain; it is a mathematical necessity arising from the quotient structure induced by limited observations.

## Implications

-   **The necessity of nominal information is a theorem, not a preference.** Any zero-error scheme must satisfy the ambiguity converse $L \ge \log_2 A_\pi$ (Theorem [\[thm:converse\]](#thm:converse){reference-type="ref" reference="thm:converse"}), where $A_\pi$ is the largest collision block induced by observable profiles. In maximal-barrier domains ($A_\pi = k$), this becomes $L \ge \log_2 k$ and nominal tagging gives the unique $D=0$ Pareto point with $W=O(1)$ (Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"}).

-   **The barrier is informational, not computational**: even with unbounded resources, attribute-only observers cannot overcome it.

-   **Fixed-axis systems are necessarily incomplete outside their axis**: by Corollary [\[cor:fixed-axis-incompleteness\]](#cor:fixed-axis-incompleteness){reference-type="ref" reference="cor:fixed-axis-incompleteness"}, any fixed-axis classifier is complete only for axis-measurable properties and cannot represent properties that vary within an axis fiber unless a new axis/tag is introduced.

-   **Classification system design is constrained**: the choice of observation family determines which properties are computable.

## Future Work

1.  **Other classification domains**: What is the matroid structure of observation spaces in chemistry (molecular fingerprints), linguistics (phonetic features), or machine learning (feature embeddings)?

2.  **Witness complexity of other properties**: Beyond identity, what are the witness costs for provenance, equivalence, or subsumption?

3.  **Hybrid observers**: Can observer strategies that combine tags and attributes achieve better $(L, W, D)$ tradeoffs for specific query distributions?

## Conclusion

Classification under observational constraints admits a clean information-theoretic analysis. The zero-error converse is governed by collision multiplicity: any $D=0$ scheme necessarily has $L \ge \log_2 A_\pi$ (Theorem [\[thm:converse\]](#thm:converse){reference-type="ref" reference="thm:converse"}). In maximal-barrier domains ($A_\pi=k$), nominal-tag observation achieves the unique Pareto-optimal $D=0$ point in the $(L, W, D)$ tradeoff (Theorem [\[thm:lwd-optimal\]](#thm:lwd-optimal){reference-type="ref" reference="thm:lwd-optimal"}). The results are universal within the stated observation model, and all proofs are machine-verified in Lean 4.

## AI Disclosure {#ai-disclosure .unnumbered}

This work was developed with AI assistance (Claude, Anthropic). The AI contributed to exposition, code generation, and proof exploration. All mathematical claims were verified by the authors and machine-checked in Lean 4. The Lean proofs are the authoritative source; no theorem depends solely on AI-generated reasoning.


## Formalization and Verification

The core claims in this paper are machine-checked in Lean 4. We keep the appendix concise for JSAIT and move full operational listings and implementation-level proof scripts to the supplementary artifact.

::: table*
  Module                            Lines                                   Theorems                     Purpose
  --------------------------------- --------------------------------------- ---------------------------- -----------------------------------------------
  `abstract_class_system.lean`                                                                           Two-axis instantiation, barrier, dominance
  `axis_framework.lean`             1821                                    63                           Query families, closure, matroid bridge
  `nominal_resolution.lean`         609                                     27                           Nominal identification and witness procedures
  `discipline_migration.lean`       142                                     11                           Discipline vs. migration consequences
  `context_formalization.lean`      215                                     7                            Greenfield/retrofit context model
  `python_instantiation.lean`       249                                     17                           Python instantiation
  `typescript_instantiation.lean`   65                                      4                            TypeScript instantiation
  `java_instantiation.lean`         63                                      4                            Java instantiation
  `rust_instantiation.lean`         64                                      4                            Rust instantiation
  `lwd_converse.lean`               64                                      4                            Zero-error converse chain on collision blocks
  **Core modules subtotal**         **+1821+609+142+215+249+65+63+64+64**   **+63+27+11+7+17+4+4+4+4**   **10 representative modules shown**
:::

#### What is in scope in the mechanization.

The formalization covers the abstract observer model, the information barrier, constant-witness vs. query lower-bound separation, matroid structure of minimal distinguishing query sets, and the $(L,W,D)$ zero-error frontier claims stated in the main text. For matroid statements, closure axioms are mechanized in `AxisClosure` (`abstract_class_system.lean`); exchange/equicardinality lemmas are mechanized in `axis_framework.lean`; and the closure-to-matroid composition is formalized there via `closureInducedAxisMatroid` and `closureInducedBasisEquicardinality` (with induced nodup/subset/exchange hypotheses explicit). For the converse in particular, `lwd_converse.lean` formalizes: `collision_block_requires_outcomes`, `collision_block_requires_bits`, `maximal_barrier_requires_bits`, and `impossible_when_bits_too_small`.

#### What is moved to supplementary artifact.

Implementation-specific operational details and extended code listings are included in supplementary material and are not required to follow the IT contribution in the main paper.

#### Artifact totals.

The complete artifact contains 26 Lean files totaling 7215 lines and 306 theorem/lemma statements; the table above highlights the core modules directly used by the main-text derivations. The remaining utility files (`Paper1.lean`, `PrintAxioms.lean`, `check_axioms.lean`, `lakefile.lean`) contribute \--609-142-215-249-65-63-64-64 lines and \--27-11-7-17-4-4-4-4 theorem/lemma statements.

## Attribute-Only Formalization {#interface-only-formalization}

Attribute-only observation is formalized by an equivalence relation on values induced by observable query responses.

``` {style="lean"}
structure InterfaceValue where
  fields : List (String * Nat)
deriving DecidableEq

def getField (obj : InterfaceValue) (name : String) : Option Nat :=
  match obj.fields.find? (fun p => p.1 == name) with
  | some p => some p.2 | none => none

def interfaceEquivalent (a b : InterfaceValue) : Prop :=
  forall name, getField a name = getField b name

def InterfaceRespecting (f : InterfaceValue -> a) : Prop :=
  forall a b, interfaceEquivalent a b -> f a = f b
```

## Corollary 6.3: Provenance Impossibility {#corollary-6.3-interface-only-cannot-provide-provenance}

Under attribute-only observation, provenance is constant on attribute-equivalence classes; therefore provenance cannot be recovered when distinct classes collide under the observable profile.

``` {style="lean"}
theorem interface_provenance_indistinguishable
    (getProvenance : InterfaceValue -> Option DuckProvenance)
    (h_interface : InterfaceRespecting getProvenance)
    (obj1 obj2 : InterfaceValue)
    (h_equiv : interfaceEquivalent obj1 obj2) :
    getProvenance obj1 = getProvenance obj2 :=
  h_interface obj1 obj2 h_equiv
```

This is the mechanized form of the main-text impossibility statement: if an observer factors through attribute profile alone, it cannot separate equal-profile values by source/provenance.

## Abstract Model Lean Formalization

The abstract model is formalized directly at the axis level and then connected to concrete instantiations.

``` {style="lean"}
-- Axis-indexed representation
abbrev Typ (A : Finset Axis) := (a : Axis) -> a \in A -> axisType a

-- Two-axis setting used in the paper
abbrev Typ2 := Typ ({Axis.Bases, Axis.Shape} : Finset Axis)

-- Projectors
abbrev projBases (t : Typ2) := t Axis.Bases (by simp)
abbrev projShape (t : Typ2) := t Axis.Shape (by simp)
```

The corresponding isomorphism theorem establishes that the two-axis representation is complete for in-scope observables in the formal model.

## Reproducibility

The full Lean development is provided in supplementary material. To verify locally:

1.  Install Lean 4 and Lake (<https://leanprover.github.io/>).

2.  From the release package root, run:

    ``` {style="lean"}
    cd proofs
    lake build
    ```

3.  Confirm successful build with no `sorry` placeholders.




---

## Machine-Checked Proofs

All theorems are formalized in Lean 4:
- Location: `docs/papers/paper1_typing_discipline/proofs/`
- Lines: 7215
- Theorems: 306
- `sorry` placeholders: 0
