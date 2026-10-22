module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.representClosure
public import DomainTheory.DataTypesAsLattices.Closures.representClosure_isScottContinuous
public import DomainTheory.DataTypesAsLattices.Closures.representClosureCode

@[expose] public section

namespace DomainTheory.DataTypesAsLattices

theorem representClosureCode_app {α : Type u} [CompleteLattice α]
    (D : CountablyAlgebraic α) (x : Pomega) :
    funOf (representClosureCode D) x = representClosure D x :=
  beta (representClosure_isScottContinuous D) x

end DomainTheory.DataTypesAsLattices
