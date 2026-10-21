/-ai
The empty set is a fixed value of the boxed sum of a and b.

This is the symmetric form of the evaluation of the boxed sum at the empty set.
ai-/
module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxPlus_typed_bot (a b : Pomega) :
    typed botElem (boxPlus a b) :=
  (boxPlus_app_bot a b).symm

end DomainTheory.DataTypesAsLattices
