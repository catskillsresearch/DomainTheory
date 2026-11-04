module

public import DomainTheory.DataTypesAsLattices.Closures.representationEncode
public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic_more
public import DomainTheory.DataTypesAsLattices.Pomega.eDense
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

namespace representationEncode

theorem fixed
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) (x : α) :
    funOf (representClosureCode D) (representationEncode D x) =
      representationEncode D x := by
  rw [representClosureCode.app]
  ext n
  change D.compact n ≤
      representationDecode D (representationEncode D x) ↔
    D.compact n ≤ x
  rw [representationDecode.encode]

end representationEncode

end DomainTheory.DataTypesAsLattices
