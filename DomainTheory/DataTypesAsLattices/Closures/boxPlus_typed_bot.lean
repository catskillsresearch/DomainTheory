module

public import Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_bot

@[expose] public section


namespace DomainTheory.DataTypesAsLattices


theorem boxPlus_typed_bot (a b : Pomega) :
    typed botElem (boxPlus a b) :=
  (boxPlus_app_bot a b).symm

end DomainTheory.DataTypesAsLattices
