module

public import DomainTheory.DataTypesAsLattices.Continuous.scottPiece
public import Mathlib.Order.SetNotation
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.SetLike

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def scottUnion (f : Pomega → Pomega) (x : Pomega) : Pomega :=
  ⋃ n, scottPiece f x n

end DomainTheory.DataTypesAsLattices
