import Mathlib.Computability.Language
import Mathlib.Computability.Encoding
import Mathlib.Computability.TMComputable

open Computability

namespace Complexity

/-- Bitstrings as lists of booleans. -/
abbrev BitStr := List Bool
/-- Languages over bitstrings. -/
abbrev Lang := Language Bool

/-- Trivial finite encoding of bitstrings: the tape alphabet is `Bool` and `encode` is the identity. -/
def bitEnc : FinEncoding BitStr :=
{ Γ := Bool
  encode := fun x => x
  decode := fun s => some s
  decode_encode := by intro x; rfl
  ΓFin := inferInstance }

/-! ## Polynomial-Time Computability

Using mathlib's Turing machine framework. `PolyTime ea eb f` means
there exists a TM that computes f in polynomial time, i.e.
`Nonempty (Turing.TM2ComputableInPolyTime ea eb f)`.
-/  

/-- "`f` is computable in polynomial time" as a Prop.
    
    This is exactly `Nonempty (Turing.TM2ComputableInPolyTime ea eb f)`,
    which means there exists a TM + polynomial bound + proof of correctness.
    
    The "polytime constructible" requirement in complexity theory maps
    directly to this definition: we have a witness, not just asymptotic claims.
-/
def PolyTime {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β) (f : α → β) : Prop :=
  Nonempty (Turing.TM2ComputableInPolyTime ea eb f)

/-- A boolean decider `d` decides language `L`. -/
def Decides (d : BitStr → Bool) (L : Lang) : Prop :=
  ∀ x, x ∈ L ↔ d x = true

/-- The class P (over bitstrings). -/
def P : Set Lang :=
  fun L =>
    ∃ d : BitStr → Bool,
      Decides d L ∧
      PolyTime bitEnc finEncodingBoolBool d

/-! ## Polynomial-Time Many-One (Karp) Reductions

The clean formalization using mathlib's Turing machine framework.
These definitions capture "polynomial-time constructible" reductions
as the existence of a polytime TM witness.

To use a reduction in a proof, you'll produce:
1. The function f : α → β
2. A witness h : Turing.TM2ComputableInPolyTime ea eb f
3. A correctness proof ∀ x, x ∈ A ↔ f x ∈ B
-/  

/-- Polynomial-time many-one (Karp) reduction between problems on encoded types.
    
    A reduction from A ⊆ α to B ⊆ β is a polynomial-time computable function f : α → β
    such that x ∈ A ↔ f(x) ∈ B.
    
    The "polytime constructible" requirement is captured by `PolyTime ea eb f`,
    which is `Nonempty (Turing.TM2ComputableInPolyTime ea eb f)`.
    -/
def ManyOneReducesPoly
    {α β : Type} (ea : FinEncoding α) (eb : FinEncoding β)
    (A : Set α) (B : Set β) : Prop :=
  ∃ f : α → β, PolyTime ea eb f ∧ ∀ x, x ∈ A ↔ f x ∈ B

/-- Karp reduction between languages over bitstrings.
    
    This is the classic many-one reduction for languages.
    `f` must be computable in polynomial time (via TM witness).
    -/
def KarpReduces (A B : Lang) : Prop :=
  ∃ f : BitStr → BitStr,
    PolyTime bitEnc bitEnc f ∧
    ∀ x, x ∈ A ↔ f x ∈ B

end Complexity
