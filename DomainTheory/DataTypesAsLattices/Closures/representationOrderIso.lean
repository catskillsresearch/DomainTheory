module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts.Fixpoints
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraic
public import DomainTheory.DataTypesAsLattices.FixedLattices.CountablyAlgebraicu2ecompact_finite_support
public import DomainTheory.DataTypesAsLattices.Graph.funOf
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode
public import DomainTheory.DataTypesAsLattices.Closures.representationDecode
public import DomainTheory.DataTypesAsLattices.Retracts.vals
public import DomainTheory.DataTypesAsLattices.Closures.representationEncode_more
@[expose] public section

namespace DomainTheory.DataTypesAsLattices

def representationOrderIso {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) :
    α ≃o Fixpoints (funOf (representClosureCode D)) where
  toFun x := ⟨representationEncode D x, representationEncode.fixed D x⟩
  invFun y := representationDecode D y
  left_inv := representationDecode.encode D
  right_inv y := by
    apply Subtype.ext
    change representationEncode D (representationDecode D y) = y
    change representClosure D y = y
    rw [← representClosureCode.app, y.property]
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rw [← representationDecode.encode D x,
        ← representationDecode.encode D y]
      apply sSup_le
      rintro _ ⟨n, hn, rfl⟩
      exact le_sSup ⟨n, h hn, rfl⟩
    · intro h n hn
      exact hn.trans h

end DomainTheory.DataTypesAsLattices
