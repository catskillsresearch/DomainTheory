module

public import Mathlib.Algebra.Ring.Parity
import all Mathlib.Algebra.Ring.Parity
public import DomainTheory.DataTypesAsLattices.Retracts
public import DomainTheory.DataTypesAsLattices.Closures.Basic
public import DomainTheory.DataTypesAsLattices.Closures.boxPlus_app_top

@[expose] public section


namespace DomainTheory.DataTypesAsLattices































theorem boxPlus_typed_top (a b : Pomega) :
    typed topElem (boxPlus a b) :=
  (boxPlus_app_top a b).symm

end DomainTheory.DataTypesAsLattices
