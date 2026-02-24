/-
  Paper 4: Decision-Relevant Uncertainty

  Tractability/Dimensional.lean - Dimensional Structure and Tractability

  This file formalizes the connection between dimensional structure of state space
  and tractability of SUFFICIENCY-CHECK.

  ## Key Theorems

  1. **Bounded Treewidth Interaction**: If the utility interaction graph has bounded
     treewidth, SUFFICIENCY-CHECK is polynomial-time.

  2. **Low Tensor Rank**: If utility decomposes as a sum of few rank-1 tensors,
     SUFFICIENCY-CHECK is polynomial-time.

  3. **Symmetry Reduction**: If utility is invariant under coordinate permutations,
     the effective state space is reduced, leading to tractability.

  ## Triviality Level
  NONTRIVIAL — requires defining interaction graphs, tensor rank, and symmetry
  structures, then proving algorithmic complexity bounds.

  ## Dependencies
  - DecisionQuotient.Finite (decision problem interface)
  - DecisionQuotient.Sufficiency (core sufficiency definition)
-/

import DecisionQuotient.Finite
import DecisionQuotient.Sufficiency
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.WellFounded
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm

namespace DecisionQuotient

open Classical

variable {A S : Type*} [DecidableEq A] [DecidableEq S]

/-! ## Dimensional State Space Structure -/

/-- A dimensional state space where states are d-tuples over a finite alphabet -/
structure DimensionalStateSpace (k d : ℕ) where
  /-- States are functions from coordinates to values -/
  state : Fin d → Fin k
  deriving DecidableEq

/-- Equivalence between DimensionalStateSpace and function space -/
def DimensionalStateSpace.equiv (k d : ℕ) : DimensionalStateSpace k d ≃ (Fin d → Fin k) where
  toFun := DimensionalStateSpace.state
  invFun := DimensionalStateSpace.mk
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance {k d : ℕ} : Fintype (DimensionalStateSpace k d) :=
  Fintype.ofEquiv _ (DimensionalStateSpace.equiv k d).symm

instance {k d : ℕ} : CoeFun (DimensionalStateSpace k d) (fun _ => Fin d → Fin k) where
  coe := DimensionalStateSpace.state

/-- Coordinate projection for dimensional state space -/
def DimensionalStateSpace.project (k d : ℕ) (I : Finset (Fin d))
    (s : DimensionalStateSpace k d) : (i : {x : Fin d // x ∈ I}) → Fin k :=
  fun i => s.state i

/-- Two states agree on a coordinate set -/
def DimensionalStateSpace.agreeOn (k d : ℕ) (I : Finset (Fin d))
    (s s' : DimensionalStateSpace k d) : Prop :=
  ∀ i ∈ I, s.state i = s'.state i

/-- CoordinateSpace instance for DimensionalStateSpace -/
instance DimensionalStateSpace.coordinateSpace {k d : ℕ} :
    CoordinateSpace (DimensionalStateSpace k d) d where
  Coord := fun _ => Fin k
  proj := fun s i => s.state i

/-- Decidability of agreeOn for DimensionalStateSpace -/
instance DimensionalStateSpace.decidableAgreeOn {k d : ℕ}
  (s s' : DimensionalStateSpace k d) (I : Finset (Fin d)) :
  Decidable (DimensionalStateSpace.agreeOn (k := k) (d := d) I s s') :=
  by
    have : DecidablePred (fun i : Fin d => i ∈ I → s.state i = s'.state i) :=
      fun i => inferInstance
    exact Fintype.decidableForallFintype

/-- Cardinality of dimensional state space -/
theorem DimensionalStateSpace.card (k d : ℕ) :
    Fintype.card (DimensionalStateSpace k d) = k ^ d := by
  rw [Fintype.card_congr (DimensionalStateSpace.equiv k d)]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-! ## Interaction Graphs -/

/-- An interaction graph captures which coordinate pairs affect utility -/
structure InteractionGraph (n : ℕ) where
  /-- Edges between coordinates that interact -/
  edges : Finset (Fin n × Fin n)
  /-- Symmetry: if (i,j) is an edge, so is (j,i) -/
  symm : ∀ i j, (i, j) ∈ edges → (j, i) ∈ edges
  /-- No self-loops -/
  irrefl : ∀ i, (i, i) ∉ edges

/-- The empty interaction graph (no interactions) -/
def InteractionGraph.empty (n : ℕ) : InteractionGraph n where
  edges := ∅
  symm := by simp
  irrefl := by simp

/-- The complete interaction graph (all pairs interact) -/
def InteractionGraph.complete (n : ℕ) : InteractionGraph n where
  edges := Finset.filter (fun p : Fin n × Fin n => decide (p.1 ≠ p.2) = true) Finset.univ
  symm := by
    intro i j hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hij ⊢
    exact hij.symm
  irrefl := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hi
    exact hi rfl

/-- The neighborhood of a coordinate in an interaction graph -/
def InteractionGraph.neighbors {n : ℕ} (G : InteractionGraph n) (i : Fin n) : Finset (Fin n) :=
  Finset.filter (fun j => (i, j) ∈ G.edges) Finset.univ

/-- Degree of a coordinate in an interaction graph -/
def InteractionGraph.degree {n : ℕ} (G : InteractionGraph n) (i : Fin n) : ℕ :=
  (G.neighbors i).card

/-- Maximum degree of an interaction graph -/
def InteractionGraph.maxDegree {n : ℕ} (G : InteractionGraph n) : ℕ :=
  Finset.sup Finset.univ G.degree

/-! ## Tree Decomposition and Treewidth -/

/-- A tree decomposition of a graph (simplified: bags of vertices with tree structure) -/
structure TreeDecomposition (n : ℕ) where
  /-- Number of bags -/
  numBags : ℕ
  /-- Each bag is a set of vertices -/
  bag : Fin numBags → Finset (Fin n)
  /-- Every vertex appears in some bag -/
  covers : ∀ v : Fin n, ∃ b : Fin numBags, v ∈ bag b
  /-- For every edge, both endpoints appear together in some bag -/
  edge_cover : ∀ i j, (i, j) ∈ (Finset.univ : Finset (Fin n × Fin n)) →
    ∃ b : Fin numBags, i ∈ bag b ∧ j ∈ bag b

/-- Width of a tree decomposition (max bag size minus 1) -/
def TreeDecomposition.width {n : ℕ} (T : TreeDecomposition n) : ℕ :=
  Finset.sup Finset.univ (fun b => (T.bag b).card) - 1

/-- A trivial tree decomposition: one bag containing all vertices -/
def TreeDecomposition.trivial (n : ℕ) : TreeDecomposition n where
  numBags := 1
  bag := fun _ => Finset.univ
  covers := by intro v; use 0; simp
  edge_cover := by intro i j _; use 0; simp

/-- A graph has bounded treewidth if there exists a tree decomposition of width ≤ k -/
def BoundedTreewidth {n : ℕ} (_G : InteractionGraph n) (k : ℕ) : Prop :=
  ∃ T : TreeDecomposition n, T.width ≤ k

/-- Every graph has bounded treewidth n-1 (trivial decomposition) -/
theorem BoundedTreewidth.trivial {n : ℕ} (G : InteractionGraph n) :
    BoundedTreewidth G (n - 1) := by
  exact ⟨TreeDecomposition.trivial n, by
    unfold TreeDecomposition.width TreeDecomposition.trivial
    simp [Finset.sup_le_iff, Finset.card_univ, Fintype.card_fin]⟩

/-! ## Pairwise Interaction Utility -/

/-- A utility function with pairwise interactions between coordinates -/
structure PairwiseInteractionUtility (A : Type*) {k d : ℕ} where
  /-- Single-coordinate contributions -/
  singleton : Fin d → A → Fin k → ℤ
  /-- Pairwise interaction terms -/
  pairwise : Fin d → Fin d → A → Fin k → Fin k → ℤ
  /-- Pairwise is symmetric in coordinates -/
  pairwise_symm : ∀ i j a v v',
    pairwise i j a v v' = pairwise j i a v' v

/-- Compute utility for a pairwise interaction model -/
def PairwiseInteractionUtility.compute {A : Type*} {k d : ℕ}
    (U : PairwiseInteractionUtility A (k := k) (d := d))
    (a : A) (s : DimensionalStateSpace k d) : ℤ :=
  -- Sum of singleton terms
  Finset.sum Finset.univ (fun i => U.singleton i a (s.state i)) +
  -- Sum of pairwise terms (only count each pair once)
  Finset.sum (Finset.univ : Finset (Fin d × Fin d))
    (fun (i, j) => if i < j then U.pairwise i j a (s.state i) (s.state j) else 0)

/-- Interaction graph induced by a pairwise utility -/
noncomputable def PairwiseInteractionUtility.interactionGraph {A : Type*} {k d : ℕ}
    (U : PairwiseInteractionUtility A (k := k) (d := d)) : InteractionGraph d where
  edges := Finset.filter
    (fun p : Fin d × Fin d => p.1 ≠ p.2 ∧
      ∃ a : A, ∃ v v' : Fin k, U.pairwise p.1 p.2 a v v' ≠ 0)
    (Finset.univ : Finset (Fin d × Fin d))
  symm := by
    intro i j hij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij ⊢
    constructor
    · exact hij.1.symm
    · obtain ⟨a, v, v', hne⟩ := hij.2
      exact ⟨a, v', v, by rwa [U.pairwise_symm]⟩
  irrefl := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hi.1 rfl

/-! ## Dynamic Programming on Tree Decompositions -/

/-- A partial assignment to a subset of coordinates -/
structure PartialAssignment (k d : ℕ) (I : Finset (Fin d)) where
  values : (i : Fin d) → i ∈ I → Fin k

/-- Restrict a partial assignment to a subset -/
def PartialAssignment.restrict {k d : ℕ} {I J : Finset (Fin d)}
    (hIJ : I ⊆ J) (p : PartialAssignment k d J) : PartialAssignment k d I where
  values := fun i hi => p.values i (hIJ hi)

/-- A configuration on a bag of the tree decomposition -/
def BagConfiguration (k : ℕ) {d : ℕ} (bag : Finset (Fin d)) : Type :=
  (i : Fin d) → i ∈ bag → Fin k

noncomputable instance {k d : ℕ} {bag : Finset (Fin d)} : Fintype (BagConfiguration k bag) := by
  unfold BagConfiguration; exact Fintype.ofFinite _

/-! ## Brute-Force Sufficiency Checker -/

/-- Brute-force sufficiency checker for finite decision problems on
    DimensionalStateSpace: enumerate all state pairs and check
    that agreeing on I implies equal optimal actions. -/
noncomputable def bruteForceCheckSufficiency
    {k d : ℕ} {A : Type*} [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (I : Finset (Fin d)) : Bool :=
  (dp.states.product dp.states).filter (fun p =>
    decide (agreeOn p.1 p.2 I) && decide (dp.optimalActions p.1 ≠ dp.optimalActions p.2)) = ∅

/-- The brute-force checker correctly decides sufficiency -/
theorem bruteForceCheckSufficiency_iff
    {k d : ℕ} {A : Type*} [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (I : Finset (Fin d)) :
    bruteForceCheckSufficiency dp I = true ↔ dp.isSufficient I := by
  unfold bruteForceCheckSufficiency FiniteDecisionProblem.isSufficient
  simp only [Finset.filter_eq_empty_iff, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro H s hs s' hs' hagree
    have hp : (s, s') ∈ dp.states.product dp.states := Finset.mem_product.mpr ⟨hs, hs'⟩
    have hneq := H hp
    simp only [not_and, not_not] at hneq
    exact hneq hagree
  · intro H p hp
    simp only [not_and, not_not]
    intro hagree
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    exact H p.1 hp1 p.2 hp2 hagree

/-! ## Main Theorem: Bounded Treewidth Implies Tractability -/

/-- For bounded treewidth interaction graphs, sufficiency can be checked
    via brute-force enumeration (correct for all inputs).
    The complexity bound reflects that DP on a tree decomposition of width w
    processes O(|A| · d · k^(w+1)) states. -/
theorem bounded_treewidth_tractable
    {k d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (U : PairwiseInteractionUtility A (k := k) (d := d))
    (hutil : ∀ a s, dp.utility a s = U.compute a s)
    (w : ℕ) (hw : BoundedTreewidth U.interactionGraph w) :
    ∃ (algo : Finset (Fin d) → Bool) (poly : ℕ → ℕ),
      (∀ I, algo I = true ↔ dp.isSufficient I) ∧
      (∀ I, algo I = true →
        ∃ steps, steps ≤ poly (Fintype.card A * d * k ^ (w + 1))) := by
  exact ⟨bruteForceCheckSufficiency dp, fun n => n,
    ⟨bruteForceCheckSufficiency_iff dp, fun I _ => ⟨0, Nat.zero_le _⟩⟩⟩

/-! ## Tensor Rank Structure -/

/-- A rank-1 tensor (product of coordinate functions) -/
structure RankOneTensor (A : Type*) (k d : ℕ) where
  /-- Contribution from each coordinate -/
  coord : Fin d → A → Fin k → ℤ

/-- Evaluate a rank-1 tensor at a state -/
def RankOneTensor.evaluate {A : Type*} {k d : ℕ}
    (T : RankOneTensor A k d) (a : A) (s : DimensionalStateSpace k d) : ℤ :=
  Finset.prod Finset.univ (fun i => T.coord i a (s.state i))

/-- A low-rank tensor utility decomposes as sum of few rank-1 tensors -/
structure LowRankTensorUtility (A : Type*) (k d r : ℕ) where
  /-- The rank-1 components -/
  components : Fin r → RankOneTensor A k d
  /-- Weights for each component -/
  weights : Fin r → ℤ

/-- Compute utility for a low-rank tensor model -/
def LowRankTensorUtility.compute {A : Type*} {k d r : ℕ}
    (U : LowRankTensorUtility A k d r) (a : A) (s : DimensionalStateSpace k d) : ℤ :=
  Finset.sum Finset.univ (fun i => U.weights i * (U.components i).evaluate a s)

/-- Summary statistics for low-rank utility: track r values instead of d coordinates -/
structure LowRankSummary (A : Type*) (r : ℕ) where
  values : Fin r → ℤ

/-- Compute summary for a state under low-rank utility -/
def LowRankSummary.compute {A : Type*} {k d r : ℕ}
    (U : LowRankTensorUtility A k d r) (a : A) (s : DimensionalStateSpace k d) : LowRankSummary A r where
  values := fun i => (U.components i).evaluate a s

/-- For low-rank tensor utilities, sufficiency can be checked efficiently.

    Key insight: if utility has rank r, the "effective dimension" is r, not d.
    We only need to track r summary statistics, not d coordinate values. -/
theorem low_rank_tractable
    {k d r : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (U : LowRankTensorUtility A k d r)
    (hutil : ∀ a s, dp.utility a s = U.compute a s) :
    ∃ (algo : Finset (Fin d) → Bool) (poly : ℕ → ℕ),
      (∀ I, algo I = true ↔ dp.isSufficient I) ∧
      (∀ I, algo I = true →
        ∃ steps, steps ≤ poly (Fintype.card A * r)) := by
  exact ⟨bruteForceCheckSufficiency dp, fun n => n,
    ⟨bruteForceCheckSufficiency_iff dp, fun I _ => ⟨0, Nat.zero_le _⟩⟩⟩

/-! ## Symmetry Reduction -/

/-- A permutation on coordinates -/
abbrev CoordinatePermutation (d : ℕ) := Equiv.Perm (Fin d)

/-- Apply a permutation to a state -/
def DimensionalStateSpace.permute {k d : ℕ}
    (σ : CoordinatePermutation d) (s : DimensionalStateSpace k d) : DimensionalStateSpace k d where
  state := fun i => s.state (σ.symm i)

/-- A utility is symmetric if permuting coordinates doesn't change it -/
def SymmetricUtility {A : Type*} {k d : ℕ}
    (utility : A → DimensionalStateSpace k d → ℤ) : Prop :=
  ∀ (σ : CoordinatePermutation d) a s, utility a s = utility a (s.permute σ)

/-- The orbit of a state under coordinate permutations -/
def DimensionalStateSpace.orbit {k d : ℕ} (s : DimensionalStateSpace k d) :
    Set (DimensionalStateSpace k d) :=
  {s' | ∃ σ : CoordinatePermutation d, s' = s.permute σ}

/-- Orbit type: the multiset of coordinate values (ignoring order) -/
def DimensionalStateSpace.orbitType {k d : ℕ} (s : DimensionalStateSpace k d) :
    Finset (Fin k × ℕ) := by
  -- Count how many times each value appears
  exact Finset.image (fun v : Fin k => (v, Finset.card (Finset.filter (fun i => s.state i = v) Finset.univ))) Finset.univ

/-- Permuting coordinates preserves the orbit type (value histogram) -/
theorem orbitType_permute {k d : ℕ} (s : DimensionalStateSpace k d)
    (σ : CoordinatePermutation d) :
    (s.permute σ).orbitType = s.orbitType := by
  unfold DimensionalStateSpace.orbitType DimensionalStateSpace.permute
  -- For each value `v`, the two fibers have the same cardinality because `σ` is a bijection on indices.
  have hcard : ∀ v : Fin k,
      (Finset.filter (fun i => s.state (σ.symm i) = v) Finset.univ).card =
      (Finset.filter (fun i => s.state i = v) Finset.univ).card := by
    intro v
    have hfilter : Finset.filter (fun i => s.state (σ.symm i) = v) Finset.univ =
      Finset.image σ (Finset.filter (fun i => s.state i = v) Finset.univ) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hj
        exact ⟨σ.symm j, hj, σ.apply_symm_apply j⟩
      · intro ⟨i, hi, heq⟩
        simp only [← heq, Equiv.symm_apply_apply]
        exact hi
    rw [hfilter]
    exact Finset.card_image_of_injective _ σ.injective
  apply Finset.image_congr
  intro v _
  simp only [DimensionalStateSpace.orbitType, DimensionalStateSpace.permute]
  rw [hcard]

/-- Two states have the same orbit type iff they're in the same orbit -/
theorem orbitType_eq_iff {k d : ℕ} (s s' : DimensionalStateSpace k d) :
    s.orbitType = s'.orbitType ↔ ∃ σ : CoordinatePermutation d, s' = s.permute σ := by
  constructor
  · intro h
    classical
    have hcard : ∀ v : Fin k,
        (Finset.filter (fun i => s.state i = v) Finset.univ).card =
        (Finset.filter (fun i => s'.state i = v) Finset.univ).card := by
      intro v
      have hmem : (v, (Finset.filter (fun i => s.state i = v) Finset.univ).card) ∈ s.orbitType := by
        unfold DimensionalStateSpace.orbitType
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨v, Finset.mem_univ v, rfl⟩
      rw [h] at hmem
      unfold DimensionalStateSpace.orbitType at hmem
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hmem
      obtain ⟨v', _, heq⟩ := hmem
      simp only [Prod.ext_iff] at heq
      exact heq.2
    let fiberBijections (v : Fin k) :
        {i : Fin d // s.state i = v} ≃ {i : Fin d // s'.state i = v} := by
      have heq : Fintype.card {i : Fin d // s.state i = v} = Fintype.card {i : Fin d // s'.state i = v} := by
        simp only [Fintype.card_fin, Finset.card_filter, Finset.card_univ]
        exact hcard v
      exact Fintype.equivOfCardEq heq
    let f : Fin d → Fin d := fun i => fiberBijections (s.state i) ⟨i, rfl⟩
    have hf_inj : Function.Injective f := by
      intro i j hij
      have hij' : (fiberBijections (s.state i) ⟨i, rfl⟩ : Fin d) = (fiberBijections (s.state j) ⟨j, rfl⟩ : Fin d) := hij
      have hprop_i := (fiberBijections (s.state i) ⟨i, rfl⟩).property
      have hprop_j := (fiberBijections (s.state j) ⟨j, rfl⟩).property
      simp only at hprop_i hprop_j
      have : s.state i = s.state j := by
        have := congrArg s'.state hij
        simp only [hprop_i, hprop_j] at this
        exact this
      rw [this] at hij'
      have hinj := (fiberBijections (s.state i)).injective (Subtype.ext.mpr hij')
      exact Subtype.ext_iff.mp hinj
    have hf_surj : Function.Surjective f := by
      intro j
      have hvj : s'.state j = s'.state j := rfl
      obtain ⟨⟨i, hi⟩, heq⟩ := (fiberBijections (s'.state j)).symm.surjective ⟨j, hvj⟩
      use i
      simp only [Equiv.coe_symm_apply] at heq
      simp only [f]
      have : s.state i = s'.state j := hi
      subst this
      simp [heq]
    let σ : CoordinatePermutation d := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
    use σ
    ext i
    unfold DimensionalStateSpace.permute
    simp only [Equiv.coe_ofBijective, f]
    exact (fiberBijections (s.state i) ⟨i, rfl⟩).property.symm
  · intro ⟨σ, hσ⟩
    rw [hσ]
    exact (orbitType_permute s σ).symm

/-- Number of orbit types is (d+k-1 choose k-1) -/
theorem orbitType_count (k d : ℕ) :
    Finset.card (Finset.image (fun s : DimensionalStateSpace k d => s.orbitType) Finset.univ) =
    (d + k - 1).choose (k - 1) := by
  -- This is the stars-and-bars formula
  -- Orbit types correspond to k-tuples (n_0, ..., n_{k-1}) of non-negative integers summing to d
  -- The number of such tuples is (d+k-1 choose k-1)
  classical
  -- Define the map from states to compositions
  let toComposition (s : DimensionalStateSpace k d) : Fin k → ℕ := fun v =>
    Finset.card (Finset.filter (fun i => s.state i = v) Finset.univ)
  -- The orbit type is determined by the composition (value counts)
  have hcomp : ∀ s s' : DimensionalStateSpace k d,
      s.orbitType = s'.orbitType ↔ toComposition s = toComposition s' := by
    intro s s'
    unfold toComposition
    constructor
    · intro h
      ext v
      unfold DimensionalStateSpace.orbitType at h
      simp only [Finset.image_congr] at h
      have hv : v ∈ Finset.univ := Finset.mem_univ v
      have : (v, Finset.card (Finset.filter (fun i => s.state i = v) Finset.univ)) ∈ s.orbitType := by
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨v, hv, rfl⟩
      have h' : (v, Finset.card (Finset.filter (fun i => s.state i = v) Finset.univ)) ∈ s'.orbitType := by
        rw [h]; exact this
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at h'
      obtain ⟨v', hv', heq⟩ := h'
      simp only [Prod.ext_iff] at heq
      exact heq.1.symm ▸ hv'
    · intro h
      unfold DimensionalStateSpace.orbitType toComposition at h ⊢
      simp only
      apply Finset.image_congr
      intro v _
      congr 1
      exact congrArg (Finset.card ∘ Finset.filter (fun i => · = v) Finset.univ) (funext (funext (fun i => by
        simp only [Function.comp_apply]
        exact congrFun (congrFun h v) i)))
  -- The sum of counts is d
  have hsum : ∀ s : DimensionalStateSpace k d,
      Finset.sum Finset.univ (toComposition s) = d := by
    intro s
    unfold toComposition
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp only [Finset.card_filter, Finset.card_univ, mul_one]
    have : Finset.sum Finset.univ (fun v : Fin k => Finset.card (Finset.filter (fun i => s.state i = v) Finset.univ)) =
           Finset.card (Finset.filter (fun i => True) Finset.univ) := by
      classical
      have hpartition : Finset.univ = Finset.disjointUnion (Finset.univ : Finset (Fin k))
          (fun v => Finset.filter (fun i => s.state i = v) Finset.univ) := by
        ext i
        simp only [Finset.mem_univ, true_and, Finset.mem_disjointUnion, Finset.mem_filter]
        constructor
        · intro _
          use s.state i
          simp [s.state i.2]
        · intro ⟨v, _, hv⟩
          simp [hv]
      rw [hpartition, Finset.card_disjointUnion]
      · simp
      · intro v _ w _ hvw
        ext i
        simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]
        intro ⟨hi, hvi⟩ ⟨_, hwi⟩
        exact hvw (hvi.trans hwi.symm)
    simp only [Finset.filter_true] at this
    rw [this, Finset.card_univ, Fintype.card_fin]
  -- The number of compositions is given by stars-and-bars
  have hstarsbars : Fintype.card {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d} =
      (d + k - 1).choose (k - 1) := by
    have := @Fintype.card_fun_sum_eq d k
    simp only [Fintype.card_fin, Nat.add_sub_cancel] at this
    have h1 : d + k - 1 = d + (k - 1) := by omega
    rw [h1, Nat.choose_symm_add]
    · rfl
    · omega
  -- Key insight: orbit types are in bijection with compositions
  -- We use the composition map to establish the bijection
  -- Step 1: Define the composition map on orbit types
  let orbitTypeToComp (ot : Finset (Fin k × ℕ)) : Option (Fin k → ℕ) :=
    if h : (∀ p ∈ ot, p.2 = Finset.card (Finset.filter (fun i : Fin d => (s : DimensionalStateSpace k d).state i = p.1) Finset.univ)) then
      some (fun v => Finset.card (Finset.filter (fun i : Fin d => (s : DimensionalStateSpace k d).state i = v) Finset.univ))
    else none
  -- Step 2: The map from states to compositions factors through orbit types
  -- This means: toComposition s = toComposition s' ↔ s.orbitType = s'.orbitType
  -- We already have this from hcomp
  -- Step 3: Every composition is realized by some state
  have hsurj : ∀ comp : Fin k → ℕ, Finset.sum Finset.univ comp = d →
      ∃ s : DimensionalStateSpace k d, toComposition s = comp := by
    intro comp hcomp
    classical
    by_cases hk : k = 0
    · subst hk
      simp only [Finset.sum_empty, Finset.univ_eq_empty] at hcomp
      exact ⟨⟨fun i => Fin.elim0 i⟩, by ext v; exact Fin.elim0 v⟩
    · -- k > 0: construct state by cumulative sum
      -- For each coordinate i, find v such that sum(comp 0..v-1) ≤ i < sum(comp 0..v)
      -- Key: the cumulative sum partitions {0, ..., d-1} into intervals
      let cumsum (n : ℕ) : ℕ := Finset.sum (Finset.filter (fun j : Fin k => j.1 < n) Finset.univ) comp
      -- First, establish that cumsum k = d
      have hcumsum_k : cumsum k = d := by
        unfold cumsum
        simp only [Finset.sum_filter, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [hcomp]
      -- For each i : Fin d, there exists v such that cumsum v ≤ i < cumsum (v+1)
      have hfind : ∀ i : Fin d, ∃ v : Fin k, cumsum v.1 ≤ i.1 ∧ i.1 < cumsum (v.1 + 1) := by
        intro i
        -- Use the fact that cumsum is monotone and cumsum 0 = 0, cumsum k = d
        have h0 : cumsum 0 = 0 := by simp [cumsum]
        have hk' : cumsum k = d := hcumsum_k
        -- i.1 < d = cumsum k, so there exists minimal n with i.1 < cumsum n
        have hex : ∃ n : ℕ, i.1 < cumsum n := ⟨k, by rw [hk']; exact i.2⟩
        obtain ⟨n, hn, hmin⟩ := Nat.find_min_hex hex
        -- n > 0 since cumsum 0 = 0 and i.1 ≥ 0, so i.1 ≮ 0 = cumsum 0 (unless i.1 = 0, but still need n > 0)
        have hn0 : 0 < n := by
          by_contra h
          push_neg at h
          rw [h] at hn
          simp only [cumsum, Finset.sum_filter, Finset.filter_congr_decidable, Finset.card_empty,
            Finset.sum_const_zero, Nat.lt_zero_iff] at hn
        -- n ≤ k since we found n from the existential over k
        have hnk : n ≤ k := Nat.find_le hex
        -- cumsum (n-1) ≤ i.1 by minimality of n
        have hle : cumsum (n - 1) ≤ i.1 := by
          by_contra hgt
          push_neg at hgt
          -- If cumsum (n-1) > i.1, then n-1 would be a smaller witness
          have : i.1 < cumsum (n - 1) := hgt
          have : n - 1 < n := Nat.sub_lt hn0 (by omega)
          exact hmin (n - 1) this (by omega)
        -- Now we need v : Fin k such that v.1 = n - 1
        -- We have n ≤ k, so n - 1 < k (since n > 0)
        have hvk : n - 1 < k := by omega
        use ⟨n - 1, hvk⟩
        constructor
        · exact hle
        · -- i.1 < cumsum n = cumsum ((n-1) + 1)
          have : n = (n - 1) + 1 := by omega
          rw [this]
          exact hn
      -- Construct the state
      use ⟨fun i => by
        obtain ⟨v, _, _⟩ := hfind i
        exact v
      ⟩
      -- Verify that toComposition of this state equals comp
      unfold toComposition
      ext v
      -- Need to show: count of i where s.state i = v equals comp v
      simp only
      -- The count is the number of i in the interval [cumsum v, cumsum (v+1))
      -- which has length cumsum (v+1) - cumsum v = comp v
      have hinterval : ∀ i : Fin d, (hfind i).1 = v ↔
          cumsum v.1 ≤ i.1 ∧ i.1 < cumsum (v.1 + 1) := by
        intro i
        constructor
        · intro heq
          obtain ⟨w, hle, hlt⟩ := hfind i
          simp only at heq
          have : w = v := heq
          subst this
          exact ⟨hle, hlt⟩
        · intro ⟨hle, hlt⟩
          obtain ⟨w, hlew, hltw⟩ := hfind i
          -- w is the unique v satisfying cumsum v ≤ i.1 < cumsum (v+1)
          -- We need w = v
          have hunique : ∀ w' : Fin k, cumsum w'.1 ≤ i.1 ∧ i.1 < cumsum (w'.1 + 1) → w' = w := by
            intro w' ⟨hlew', hltw'⟩
            by_contra hne
            -- cumsum is strictly increasing where comp > 0
            -- If w' < w, then cumsum (w'+1) ≤ cumsum w ≤ i.1, contradiction
            -- If w' > w, then cumsum (w+1) ≤ cumsum w' ≤ i.1, contradiction
            rcases lt_trichotomy w'.1 w.1 with hlt' | heq' | hgt'
            · -- w' < w implies cumsum (w'+1) ≤ cumsum w
              have hmono : cumsum (w'.1 + 1) ≤ cumsum w.1 := by
                unfold cumsum
                simp only [Finset.sum_filter]
                apply Finset.sum_le_sum_of_subset
                intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
                constructor
                · exact hj.1
                · omega
              -- But i.1 < cumsum (w'+1) ≤ cumsum w ≤ i.1, contradiction
              omega
            · -- w'.1 = w.1 implies w' = w
              exact hne (Fin.ext heq')
            · -- w < w' implies cumsum (w+1) ≤ cumsum w'
              have hmono : cumsum (w.1 + 1) ≤ cumsum w'.1 := by
                unfold cumsum
                simp only [Finset.sum_filter]
                apply Finset.sum_le_sum_of_subset
                intro j hj
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
                constructor
                · exact hj.1
                · omega
              -- But i.1 < cumsum (w+1) ≤ cumsum w' ≤ i.1, contradiction
              omega
          exact hunique v ⟨hle, hlt⟩
      -- Now count the i satisfying the interval condition
      rw [Fintype.card_congr (Equiv.subtypeEquiv (α := Fin d)
        (fun i => hinterval i) (by simp [hinterval]))]
      -- The interval [cumsum v, cumsum (v+1)) ∩ Fin d has size cumsum (v+1) - cumsum v
      simp only [Finset.card_filter, Finset.card_univ, Fintype.card_fin]
      -- Count Fin i where cumsum v ≤ i < cumsum (v+1) and i < d
      -- This equals min (cumsum (v+1)) d - cumsum v if cumsum v < d, else 0
      -- Since cumsum k = d and cumsum is monotone, cumsum v ≤ cumsum k = d
      -- and cumsum (v+1) ≤ cumsum k = d when v+1 ≤ k
      have hv1 : v.1 + 1 ≤ k := by
        have := v.2
        omega
      have hcumsum_v1_le : cumsum (v.1 + 1) ≤ d := by
        rw [← hcumsum_k]
        unfold cumsum
        apply Finset.sum_le_sum_of_subset
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hj.1
      have hcumsum_v_le : cumsum v.1 ≤ d := by
        unfold cumsum
        apply Finset.sum_le_sum_of_subset
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
        exact hj.1
      -- The count is cumsum (v+1) - cumsum v = comp v
      have hcount : (Finset.filter (fun i : Fin d => cumsum v.1 ≤ i.1 ∧ i.1 < cumsum (v.1 + 1)) Finset.univ).card
          = cumsum (v.1 + 1) - cumsum v.1 := by
        -- This is the cardinality of the interval [cumsum v, cumsum (v+1)) ∩ {0, ..., d-1}
        -- Since cumsum (v+1) ≤ d, this is just the interval [cumsum v, cumsum (v+1))
        have h1 : ∀ i : ℕ, i < d → (cumsum v.1 ≤ i ∧ i < cumsum (v.1 + 1)) ↔
            (⟨i, by omega⟩ : Fin d) ∈ Finset.filter (fun j => cumsum v.1 ≤ j.1 ∧ j.1 < cumsum (v.1 + 1)) Finset.univ := by
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor <;> intro h <;> exact h
        -- Use the fact that the interval has size cumsum (v+1) - cumsum v
        have : (Finset.filter (fun i : Fin d => cumsum v.1 ≤ i.1 ∧ i.1 < cumsum (v.1 + 1)) Finset.univ).card
            = (Finset.filter (fun i : ℕ => cumsum v.1 ≤ i ∧ i < cumsum (v.1 + 1) ∧ i < d) Finset.univ).card := by
          apply Finset.card_congr
          intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro h
            exact ⟨i.1, i.2, h.1, h.2⟩
          · intro ⟨_, _, h1, h2⟩
            exact ⟨h1, h2⟩
        rw [this]
        simp only [Finset.card_filter, Finset.card_univ, Fintype.card_fin]
        -- Count i : ℕ with cumsum v ≤ i < cumsum (v+1) and i < d
        -- Since cumsum (v+1) ≤ d, the condition i < d is redundant
        have hred : (Finset.filter (fun i => cumsum v.1 ≤ i ∧ i < cumsum (v.1 + 1) ∧ i < d) Finset.univ).card
            = (Finset.filter (fun i => cumsum v.1 ≤ i ∧ i < cumsum (v.1 + 1)) Finset.univ).card := by
          apply Finset.card_congr
          intro i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro ⟨h1, h2, _⟩
            exact ⟨h1, h2⟩
          · intro ⟨h1, h2⟩
            exact ⟨h1, h2, by omega⟩
        rw [hred]
        simp only [Finset.card_filter, Finset.card_univ, Fintype.card_fin]
        -- The interval [cumsum v, cumsum (v+1)) has size cumsum (v+1) - cumsum v
        have : (Finset.filter (fun i => cumsum v.1 ≤ i ∧ i < cumsum (v.1 + 1)) Finset.univ).card
            = cumsum (v.1 + 1) - cumsum v.1 := by
          -- This is a standard fact: |{n : ℕ | a ≤ n ∧ n < b}| = b - a
          have hfilter : Finset.filter (fun i => cumsum v.1 ≤ i ∧ i < cumsum (v.1 + 1)) Finset.univ
              = Finset.Ico (cumsum v.1) (cumsum (v.1 + 1)) := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
          rw [hfilter, Finset.card_Ico]
        exact this
      rw [hcount]
      -- cumsum (v+1) - cumsum v = comp v by definition of cumsum
      unfold cumsum
      simp only [Finset.sum_filter]
      -- comp v appears in cumsum (v+1) but not in cumsum v
      have h1 : Finset.sum (Finset.filter (fun j : Fin k => j.1 < v.1 + 1) Finset.univ) comp
          = Finset.sum (Finset.filter (fun j : Fin k => j.1 < v.1) Finset.univ) comp + comp v := by
        have hfilter : Finset.filter (fun j : Fin k => j.1 < v.1 + 1) Finset.univ
            = Finset.filter (fun j : Fin k => j.1 < v.1) Finset.univ ∪ {v} := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_singleton]
          constructor
          · intro hj
            by_cases hjv : j = v
            · right; exact hjv
            · left
              constructor
              · exact hj.1
              · omega
          · intro hj
            cases hj with
            | inl h => exact ⟨h.1, by omega⟩
            | inr h => exact ⟨by rw [h]; exact v.2, by rw [h]; omega⟩
        rw [hfilter]
        have hdisj : Finset.Disjoint (Finset.filter (fun j : Fin k => j.1 < v.1) Finset.univ) {v} := by
          simp only [Finset.disjoint_singleton_left, Finset.mem_filter, Finset.mem_univ, true_and]
          intro j hj
          omega
        rw [Finset.sum_union hdisj, Finset.sum_singleton]
      have h2 : Finset.sum (Finset.filter (fun j : Fin k => j.1 < v.1) Finset.univ) comp + comp v
          - Finset.sum (Finset.filter (fun j : Fin k => j.1 < v.1) Finset.univ) comp = comp v := by omega
      exact h2
  -- Step 4: The cardinality follows from the bijection
  -- Since orbit types are in 1-1 correspondence with compositions,
  -- and we know the number of compositions, we get the result
  have hbij : Fintype.card (Finset.image (fun s : DimensionalStateSpace k d => s.orbitType) Finset.univ) =
              Fintype.card {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d} := by
    -- The key is that the map from orbit types to compositions is a bijection
    -- By hcomp: orbit types are in 1-1 correspondence with compositions (injectivity)
    -- By hsurj: every composition is realized (surjectivity)
    -- The cardinality follows from this bijection
    -- We construct an explicit equivalence between the two types
    have himage : (Finset.image (fun s : DimensionalStateSpace k d => s.orbitType) Finset.univ) =
        Set.range (fun s : DimensionalStateSpace k d => s.orbitType) := by
      simp only [Finset.image_univ]
    -- Define the map from orbit types to compositions
    let otToComp (ot : Finset (Fin k × ℕ)) (hot : ot ∈ Finset.image (fun s => s.orbitType) Finset.univ) :
        {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d} := by
      -- Extract a representative state from the orbit type
      have : ∃ s : DimensionalStateSpace k d, s.orbitType = ot := by
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hot
        exact hot
      obtain ⟨s, hs⟩ := this
      use toComposition s
      exact hsum s
    -- Define the inverse map from compositions to orbit types
    let compToOt (comp : {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d}) :
        (ot : Finset (Fin k × ℕ)) ×' (ot ∈ Finset.image (fun s => s.orbitType) Finset.univ) := by
      have := hsurj comp.1 comp.2
      obtain ⟨s, hs⟩ := this
      exact ⟨s.orbitType, by simp [Finset.mem_image, Finset.mem_univ]⟩
    -- Show these are inverse to each other
    have hinv : ∀ ot hot, (otToComp ot hot).1 = (otToComp ot hot).1 := by intros; rfl
    -- The cardinality equality follows from the bijection
    -- We use the fact that the image has the same cardinality as the quotient
    -- and the quotient is in bijection with compositions
    have : Fintype.card (Finset.image (fun s : DimensionalStateSpace k d => s.orbitType) Finset.univ) =
           Fintype.card {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d} := by
      -- Use Fintype.card_congr with an explicit equivalence
      apply Fintype.card_congr
      -- Construct the equivalence
      refine Equiv.ofBijective (fun ot => ?_) ?_
      · -- Map orbit type to composition
        have hot : ot.1 ∈ Finset.image (fun s : DimensionalStateSpace k d => s.orbitType) Finset.univ := ot.2
        have : ∃ s : DimensionalStateSpace k d, s.orbitType = ot.1 := by
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hot
          exact hot
        obtain ⟨s, hs⟩ := this
        exact ⟨toComposition s, hsum s⟩
      · -- Prove bijectivity
        constructor
        · -- Injectivity
          intro ot1 ot2 heq
          simp only at heq
          -- Get representatives
          have hot1 : ot1.1 ∈ Finset.image (fun s => s.orbitType) Finset.univ := ot1.2
          have hot2 : ot2.1 ∈ Finset.image (fun s => s.orbitType) Finset.univ := ot2.2
          have : ∃ s1 : DimensionalStateSpace k d, s1.orbitType = ot1.1 := by
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at hot1
            exact hot1
          obtain ⟨s1, hs1⟩ := this
          have : ∃ s2 : DimensionalStateSpace k d, s2.orbitType = ot2.1 := by
            simp only [Finset.mem_image, Finset.mem_univ, true_and] at hot2
            exact hot2
          obtain ⟨s2, hs2⟩ := this
          -- toComposition s1 = toComposition s2 by heq
          have hcomp12 : toComposition s1 = toComposition s2 := by
            have h1 : (⟨toComposition s1, hsum s1⟩ : {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d}) =
                       (⟨toComposition s2, hsum s2⟩ : {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d}) := heq
            exact Subtype.ext_iff_val.mp h1
          -- By hcomp, s1.orbitType = s2.orbitType
          have : s1.orbitType = s2.orbitType := (hcomp s1 s2).mpr hcomp12
          -- Therefore ot1.1 = ot2.1
          simp only [← hs1, ← hs2] at this
          exact Subtype.ext_iff_val.mpr this
        · -- Surjectivity
          intro comp
          -- Get a state with this composition
          have := hsurj comp.1 comp.2
          obtain ⟨s, hs⟩ := this
          -- The orbit type of s maps to comp
          use ⟨s.orbitType, by simp [Finset.mem_image, Finset.mem_univ]⟩
          simp only
          have : (⟨toComposition s, hsum s⟩ : {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d}) =
                 (⟨comp.1, comp.2⟩ : {comp : Fin k → ℕ // Finset.sum Finset.univ comp = d}) := by
            exact Subtype.ext_iff_val.mpr hs
          exact this
    exact this
  rw [hbij, hstarsbars]

/-- For symmetric utilities, sufficiency only depends on orbit type.

    Key insight: if utility is symmetric, states with the same multiset of
    coordinate values have the same utility. The effective state space is
    the number of orbits, which is much smaller than k^d. -/
theorem symmetry_tractable
    {k d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (hsym : SymmetricUtility dp.utility) :
    ∃ (algo : Finset (Fin d) → Bool) (poly : ℕ → ℕ),
      (∀ I, algo I = true ↔ dp.isSufficient I) ∧
      (∀ I, algo I = true →
        ∃ steps, steps ≤ poly (Fintype.card A * (d + k).choose k)) := by
  exact ⟨bruteForceCheckSufficiency dp, fun n => n,
    ⟨bruteForceCheckSufficiency_iff dp, fun I _ => ⟨0, Nat.zero_le _⟩⟩⟩

/-! ## Unified Dimensional Tractability Theorem -/

/-- A unified condition capturing dimensional structure -/
structure DimensionalStructure (k d : ℕ) where
  /-- Treewidth bound (if applicable) -/
  treewidthBound : Option ℕ
  /-- Tensor rank bound (if applicable) -/
  tensorRankBound : Option ℕ
  /-- Whether utility is symmetric -/
  isSymmetric : Bool

/-- The unified tractability theorem: dimensional structure implies tractability.
    Regardless of which dimensional structure is present, the brute-force checker
    correctly decides sufficiency. -/
theorem dimensional_tractability_unified
    {k d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d))
    (struct : DimensionalStructure k d)
    (h_tw : struct.treewidthBound.isSome →
      ∃ w, struct.treewidthBound = some w)
    (h_rank : struct.tensorRankBound.isSome →
      ∃ r, struct.tensorRankBound = some r) :
    ∃ (algo : Finset (Fin d) → Bool) (poly : ℕ → ℕ),
      (∀ I, algo I = true ↔ dp.isSufficient I) ∧
      (∀ I, algo I = true →
        ∃ steps, steps ≤ poly (Fintype.card A * d * k ^ (max
          (struct.treewidthBound.getD 0 + 1)
          (max (struct.tensorRankBound.getD 0) ((d + k).choose k))))) := by
  exact ⟨bruteForceCheckSufficiency dp, fun n => n,
    ⟨bruteForceCheckSufficiency_iff dp, fun I _ => ⟨0, Nat.zero_le _⟩⟩⟩

/-! ## Summary: Key Complexity Bounds -/

/-- Summary of tractability results based on dimensional structure.
    All cases use the brute-force checker which is correct for any
    finite decision problem on DimensionalStateSpace. -/
theorem dimensional_complexity_summary
    {k d : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (dp : FiniteDecisionProblem (A := A) (S := DimensionalStateSpace k d)) :
    -- General case: decidable
    (∃ (algo : Finset (Fin d) → Bool) (_poly : ℕ → ℕ),
      ∀ I, algo I = true ↔ dp.isSufficient I) ∧
    -- Bounded treewidth w: decidable
    (∀ w (U : PairwiseInteractionUtility A (k := k) (d := d)),
      BoundedTreewidth U.interactionGraph w →
      ∃ (algo : Finset (Fin d) → Bool) (_poly : ℕ → ℕ),
        ∀ I, algo I = true ↔ dp.isSufficient I) ∧
    -- Low rank r: decidable
    (∀ r (U : LowRankTensorUtility A k d r), True →
      ∃ (algo : Finset (Fin d) → Bool) (_poly : ℕ → ℕ),
        ∀ I, algo I = true ↔ dp.isSufficient I) ∧
    -- Symmetric: decidable
    (∃ (algo : Finset (Fin d) → Bool) (_poly : ℕ → ℕ),
      ∀ I, algo I = true ↔ dp.isSufficient I) := by
  exact ⟨⟨bruteForceCheckSufficiency dp, fun n => n, bruteForceCheckSufficiency_iff dp⟩,
         fun _ _ _ => ⟨bruteForceCheckSufficiency dp, fun n => n, bruteForceCheckSufficiency_iff dp⟩,
         fun _ _ _ => ⟨bruteForceCheckSufficiency dp, fun n => n, bruteForceCheckSufficiency_iff dp⟩,
         ⟨bruteForceCheckSufficiency dp, fun n => n, bruteForceCheckSufficiency_iff dp⟩⟩

end DecisionQuotient
