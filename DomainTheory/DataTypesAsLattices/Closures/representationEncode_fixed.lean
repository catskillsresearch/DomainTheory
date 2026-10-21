/-ai
The encoding of an element is a fixed point of the representing-closure code.

Applying the code is the representing closure. An index lies in that closure exactly when the corresponding compact element lies below the decoding of the encoding, and that decoding equals the original element, which is membership in the encoding.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
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
