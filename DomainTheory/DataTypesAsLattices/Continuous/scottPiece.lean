module

public import DomainTheory.DataTypesAsLattices.Pomega.e
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def scottPiece (f : Pomega → Pomega) (x : Pomega) (n : ℕ) : Pomega :=
  {k | e n ⊆ x ∧ k ∈ f (e n)}

end DomainTheory.DataTypesAsLattices
