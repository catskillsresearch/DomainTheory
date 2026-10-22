module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode_app
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode_encode

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem representationEncode_fixed
    {α : Type u} [CompleteLattice α] (D : CountablyAlgebraic α) (x : α) :
    funOf (representClosureCode D) (representationEncode D x) =
      representationEncode D x := by
  rw [representClosureCode_app]
  ext n
  change D.compact n ≤
      representationDecode D (representationEncode D x) ↔
    D.compact n ≤ x
  rw [representationDecode_encode]

end DomainTheory.DataTypesAsLattices
