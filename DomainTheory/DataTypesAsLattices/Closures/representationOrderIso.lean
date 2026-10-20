/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
-/
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

set_option linter.unusedSectionVars false

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
