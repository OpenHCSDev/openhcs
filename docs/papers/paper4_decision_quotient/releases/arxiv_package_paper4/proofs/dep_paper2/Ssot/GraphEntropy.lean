import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Ssot.Entropy

open scoped BigOperators

namespace Ssot
namespace GraphEntropy

structure VertexDist (α : Type*) [Fintype α] where
  prob : α → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_one : ∑ a, prob a = 1

namespace VertexDist

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

noncomputable def support [DecidableEq α] (p : VertexDist α) : Finset α :=
  Finset.univ.filter fun a => 0 < p.prob a

noncomputable def supportSize [DecidableEq α] (p : VertexDist α) : ℕ :=
  p.support.card

noncomputable def entropy (p : VertexDist α) : ℝ :=
  -∑ a, entropyTerm (p.prob a)

noncomputable def pushforward (p : VertexDist α) (f : α → β) : VertexDist β where
  prob := fun b => Finset.sum (Finset.univ.filter (fun a => f a = b)) fun a => p.prob a
  nonneg b := by
    refine Finset.sum_nonneg ?_
    intro a ha
    exact p.nonneg a
  sum_one := by
    classical
    calc
      ∑ b, Finset.sum (Finset.univ.filter (fun a => f a = b)) (fun a => p.prob a)
          = ∑ b, Finset.sum Finset.univ (fun a => if f a = b then p.prob a else 0) := by
              simp_rw [Finset.sum_filter]
      _ = ∑ a, Finset.sum Finset.univ (fun b => if f a = b then p.prob a else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ a, p.prob a := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [eq_comm]
      _ = 1 := p.sum_one

end VertexDist

section Coloring

variable {α : Type*} [Fintype α] [DecidableEq α]

def IsProperColoring (G : SimpleGraph α) (n : ℕ) (c : α → Fin n) : Prop :=
  ∀ ⦃u v : α⦄, G.Adj u v → c u ≠ c v

noncomputable def coloringEntropy (G : SimpleGraph α)
    (p : VertexDist α) {n : ℕ} (c : α → Fin n) : ℝ :=
  (p.pushforward c).entropy

noncomputable def chromaticEntropySet (G : SimpleGraph α) (p : VertexDist α) : Set ℝ :=
  {r | ∃ n, ∃ c : α → Fin n, IsProperColoring G n c ∧ coloringEntropy G p c = r}

noncomputable def chromaticEntropy (G : SimpleGraph α) (p : VertexDist α) : ℝ :=
  sInf (chromaticEntropySet G p)

theorem properColoring_injOn_clique {G : SimpleGraph α} {n : ℕ}
    (c : α → Fin n) (hc : IsProperColoring G n c)
    {s : Finset α} (hs : G.IsClique (↑s : Set α)) :
    Set.InjOn c (↑s : Set α) := by
  intro u hu v hv huv
  by_cases hneq : u = v
  · exact hneq
  · have hadj : G.Adj u v := hs hu hv hneq
    exact False.elim <| (hc hadj) huv

theorem clique_card_le_colors {G : SimpleGraph α} {n : ℕ}
    (c : α → Fin n) (hc : IsProperColoring G n c)
    {s : Finset α} (hs : G.IsClique (↑s : Set α)) :
    s.card ≤ n := by
  classical
  have hinj : Set.InjOn c (↑s : Set α) := properColoring_injOn_clique c hc hs
  have himage : (s.image c).card = s.card := by
    exact Finset.card_image_of_injOn fun a ha b hb hab => hinj ha hb hab
  have hbound : (s.image c).card ≤ n := by
    simpa using (Finset.card_le_univ (s := s.image c))
  exact himage.ge.trans hbound

theorem complete_graph_needs_all_colors {n m : ℕ} (c : Fin n → Fin m)
    (hc : IsProperColoring (⊤ : SimpleGraph (Fin n)) m c) :
    n ≤ m := by
  classical
  let s : Finset (Fin n) := Finset.univ
  have hs : (⊤ : SimpleGraph (Fin n)).IsClique (↑s : Set (Fin n)) := by
    intro u hu v hv huv
    simpa using huv
  simpa [s] using clique_card_le_colors c hc hs

end Coloring

end GraphEntropy
end Ssot
