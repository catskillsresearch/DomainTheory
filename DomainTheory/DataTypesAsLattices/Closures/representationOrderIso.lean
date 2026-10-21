/-ai
Scott's representation order isomorphism sends an element of a countably algebraic lattice to the fixed point given by its encoding, and the inverse decodes a fixed point. Decoding after encoding is the identity. Encoding after decoding is the representing closure of the fixed point, which equals the point because applying the representing-closure code is that closure and the point is fixed by the code. The encoding of one element is contained in the encoding of another exactly when the first lies below the second: the forward comparison decodes both encodings and lifts each compact element below the first along the inclusion of indices, and the reverse comparison uses that a compact element below the first remains below the second.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode_app
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode_encode
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode_fixed

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

/-- The order isomorphism in Scott's representation theorem. -/
def representationOrderIso {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    α ≃o Fixpoints (funOf (representClosureCode D)) where
  toFun x := ⟨representationEncode D x, representationEncode_fixed D x⟩
  invFun y := representationDecode D y
  left_inv := representationDecode_encode D
  right_inv y := by
    apply Subtype.ext
    change representationEncode D (representationDecode D y) = y
    change representClosure D y = y
    rw [← representClosureCode_app, y.property]
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rw [← representationDecode_encode D x,
        ← representationDecode_encode D y]
      apply sSup_le
      rintro _ ⟨n, hn, rfl⟩
      exact le_sSup ⟨n, h hn, rfl⟩
    · intro h n hn
      exact hn.trans h

end DomainTheory.DataTypesAsLattices
